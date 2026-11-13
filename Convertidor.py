#!/usr/bin/env python3
import sys


# ----------------------------------------------------------------------------
# Comprobación previa de versión (antes de importar nada que pueda fallar)
# ----------------------------------------------------------------------------
def _salir_con_aviso(msg):
    linea = "=" * 60
    print(f"\n{linea}\n❌ NO SE PUDO EJECUTAR EL SCRIPT\n{linea}", file=sys.stderr)
    print(msg, file=sys.stderr)
    print(linea, file=sys.stderr)
    try:
        input("\nPulsa Enter para cerrar...")
    except BaseException:
        pass
    sys.exit(1)


if sys.version_info < (3, 7):
    _salir_con_aviso("Tipo de error : PYTHON DEMASIADO ANTIGUO\n"
                     "Posible causa : Este script necesita Python 3.7 o superior.\n"
                     f"Detalle       : Tienes Python {sys.version.split()[0]}")

# Evita que un carácter raro rompa los print (consolas antiguas de Windows)
for _flujo in (sys.stdout, sys.stderr):
    try:
        _flujo.reconfigure(errors="replace")
    except Exception:
        pass

import argparse
import codecs
import csv
import io
import os
import re
import tempfile
import traceback
import xml.etree.ElementTree as ET
from datetime import datetime

NOMBRE_CSV = 'incidencies.csv'
NOMBRE_XML = 'incidencies.xml'
ERROR_LOG = 'error_convertidor.log'
MAX_BYTES = 200 * 1024 * 1024          # no se intenta leer CSV de más de 200 MB
MAX_AVISOS_VISIBLES = 5
LIMITE_CAMPO_CSV = 50 * 1024 * 1024    # tamaño máximo de una celda

# Caracteres que NO pueden aparecer jamás en un XML 1.0
RE_XML_INVALIDO = re.compile('[\x00-\x08\x0b\x0c\x0e-\x1f\ud800-\udfff\ufffe\uffff]')
# Caracteres permitidos en un nombre de etiqueta (se excluyen × y ÷, que XML no admite)
RE_NO_PERMITIDO = re.compile(r'[^A-Za-z0-9_.\-\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u024F]')
RE_INICIO_VALIDO = re.compile(r'^[A-Za-z_\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u024F]')


class ErrorConvertidor(Exception):
    """Error previsto: se muestra con formato [ERROR] y el programa termina."""


# ----------------------------------------------------------------------------
# Avisos (no detienen el programa)
# ----------------------------------------------------------------------------
_avisos = {"n": 0}


def aviso(msg):
    _avisos["n"] += 1
    if _avisos["n"] <= MAX_AVISOS_VISIBLES:
        print(f"[AVISO] {msg}")


def resumen_avisos():
    extra = _avisos["n"] - MAX_AVISOS_VISIBLES
    if extra > 0:
        print(f"[AVISO] ... y {extra} aviso(s) más.")


# ----------------------------------------------------------------------------
# Limpieza de textos y etiquetas
# ----------------------------------------------------------------------------
def limpiar_texto(valor):
    """Quita los caracteres prohibidos en XML (si no, el XML saldría corrupto)."""
    return RE_XML_INVALIDO.sub('', '' if valor is None else str(valor))


def netejar_etiqueta(nom, posicion=1):
    """Convierte un nombre de columna en un nombre de etiqueta XML válido."""
    nom = limpiar_texto(nom)
    nom = re.sub(r'\s+', '_', nom.strip())
    nom = RE_NO_PERMITIDO.sub('', nom)
    if not nom:
        return f"columna_{posicion}"
    if not RE_INICIO_VALIDO.match(nom):
        nom = '_' + nom
    if nom.lower().startswith('xml'):      # nombres reservados por el estándar
        nom = '_' + nom
    return nom[:100]


def nombres_unicos(cabecera):
    """Etiquetas válidas y sin repetir (dos columnas iguales darían XML ambiguo)."""
    usados, resultado = set(), []
    for i, crudo in enumerate(cabecera, start=1):
        base = netejar_etiqueta(crudo, i)
        nom, k = base, 2
        while nom in usados:
            nom = f"{base}_{k}"
            k += 1
        if not (crudo or '').strip():
            aviso(f"La columna {i} no tiene nombre: se llamará '{nom}'.")
        elif nom != base:
            aviso(f"Columna repetida '{crudo.strip()}': la {i}ª se llamará '{nom}'.")
        usados.add(nom)
        resultado.append(nom)
    return resultado, usados


# ----------------------------------------------------------------------------
# Lectura del CSV
# ----------------------------------------------------------------------------
def subir_limite_csv():
    try:
        csv.field_size_limit(LIMITE_CAMPO_CSV)
    except (OverflowError, ValueError):
        pass


def validar_entrada(csv_path):
    if os.path.isdir(csv_path):
        raise ErrorConvertidor(f"'{csv_path}' es una carpeta, no un archivo CSV.")
    if not os.path.isfile(csv_path):
        raise ErrorConvertidor(f"No se ha encontrado el archivo CSV: {csv_path}\n"
                               f"Asegúrate de que '{NOMBRE_CSV}' está en la misma carpeta "
                               "que Convertidor.py")


def leer_bytes(csv_path):
    try:
        tam = os.path.getsize(csv_path)
        if tam == 0:
            raise ErrorConvertidor(f"El archivo {csv_path} está vacío (0 bytes).")
        if tam > MAX_BYTES:
            raise ErrorConvertidor(f"El archivo pesa {tam / 1048576:.0f} MB; "
                                   f"el máximo admitido es {MAX_BYTES // 1048576} MB.")
        with open(csv_path, 'rb') as f:
            return f.read()
    except PermissionError:
        raise ErrorConvertidor(f"Sin permiso para leer {csv_path} "
                               "(¿está abierto en otro programa?).")
    except OSError as e:
        raise ErrorConvertidor(f"No se pudo leer {csv_path}: {e}")


def decodificar(datos):
    """Detecta la codificación (UTF-8, UTF-8 con BOM, UTF-16, Windows-1252...)."""
    if datos.startswith(b'PK\x03\x04'):
        raise ErrorConvertidor("El archivo parece un Excel (.xlsx) o un comprimido, no un CSV.\n"
                               "Ábrelo y usa Guardar como > CSV UTF-8.")
    if datos.startswith(b'\xd0\xcf\x11\xe0'):
        raise ErrorConvertidor("El archivo parece un Excel antiguo (.xls), no un CSV.\n"
                               "Ábrelo y usa Guardar como > CSV UTF-8.")
    if datos.startswith(b'%PDF'):
        raise ErrorConvertidor("El archivo es un PDF, no un CSV.")

    if datos.startswith(codecs.BOM_UTF8):
        candidatos = ['utf-8-sig', 'cp1252']
    elif datos.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)):
        candidatos = ['utf-16']
    else:
        if b'\x00' in datos[:8192]:
            raise ErrorConvertidor("El archivo parece binario, no un CSV de texto.")
        candidatos = ['utf-8', 'cp1252']

    for cod in candidatos:
        try:
            texto = datos.decode(cod)
            break
        except UnicodeDecodeError:
            continue
    else:
        cod = 'latin-1'
        texto = datos.decode('latin-1')
        aviso("No se pudo detectar la codificación; se ha usado latin-1 "
              "(algún acento podría verse mal).")

    texto = texto.replace('\x00', '').lstrip('\ufeff')
    return texto, cod


def detectar_delimitador(texto):
    """Devuelve (delimitador, texto). Soporta , ; tabulador | y la línea 'sep=;' de Excel."""
    m = re.match(r'\s*sep=(.)[ \t]*\r?\n', texto, re.I)
    if m:
        return m.group(1), texto[m.end():]
    primera = next((l for l in texto.splitlines() if l.strip()), '')
    mejor, mejor_n = ',', 1
    for d in (',', ';', '\t', '|'):
        try:
            n = len(next(csv.reader([primera], delimiter=d)))
        except (csv.Error, StopIteration):
            continue
        if n > mejor_n:
            mejor, mejor_n = d, n
    return mejor, texto


def _leer_filas(texto, delim, estricto):
    """Devuelve (cabecera, filas, vacias) o lanza csv.Error si hay comillas mal puestas."""
    lector = csv.reader(io.StringIO(texto, newline=''), delimiter=delim, strict=estricto)
    cabecera, filas, vacias = None, [], 0
    try:
        for fila in lector:
            if not fila:
                continue                      # línea en blanco
            if cabecera is None:
                if any(c.strip() for c in fila):
                    cabecera = fila
                continue
            if not any(c.strip() for c in fila):
                vacias += 1                   # fila con solo separadores
                continue
            filas.append(fila)
    except csv.Error as e:
        raise csv.Error(f"línea {lector.line_num}: {e}")
    return cabecera, filas, vacias


def parsear_csv(texto, delim):
    """Devuelve (cabecera, filas). Primero lee en modo estricto; si hay comillas
    mal cerradas, relee en modo tolerante y avisa de que el resultado puede ser incorrecto."""
    try:
        cabecera, filas, vacias = _leer_filas(texto, delim, True)
    except csv.Error as e_estricto:
        try:
            cabecera, filas, vacias = _leer_filas(texto, delim, False)
        except csv.Error as e:
            raise ErrorConvertidor(f"CSV mal formado ({e}).")
        aviso(f"El CSV tiene comillas mal cerradas o mal puestas ({e_estricto}). "
              "Se ha leído en modo tolerante: REVISA el resultado, algunas filas "
              "podrían haberse mezclado.")
    if vacias:
        aviso(f"Se han ignorado {vacias} fila(s) completamente vacías.")
    return cabecera, filas


def recortar_columnas_vacias(cabecera, filas):
    """Quita columnas finales sin nombre y sin datos (típico de una coma de más)."""
    while cabecera and not cabecera[-1].strip():
        pos = len(cabecera) - 1
        if any(len(f) > pos and f[pos].strip() for f in filas):
            break
        cabecera.pop()
    return cabecera


# ----------------------------------------------------------------------------
# Construcción y escritura del XML
# ----------------------------------------------------------------------------
def _indentar(elem, nivel=0, espacio='    '):
    """Indentado manual (ET.indent solo existe desde Python 3.9)."""
    hijos = list(elem)
    if not hijos:
        return
    if not (elem.text or '').strip():
        elem.text = '\n' + espacio * (nivel + 1)
    for h in hijos:
        _indentar(h, nivel + 1, espacio)
        if not (h.tail or '').strip():
            h.tail = '\n' + espacio * (nivel + 1)
    hijos[-1].tail = '\n' + espacio * nivel


def construir_xml(cabecera, filas):
    cabecera = recortar_columnas_vacias(list(cabecera), filas)
    nombres, usados = nombres_unicos(cabecera)
    ncols = len(nombres)

    # Celdas sobrantes: solo se conservan si traen datos reales
    max_len = max((len(f) for f in filas), default=ncols)
    extras = {}
    for j in range(ncols, max_len):
        if any(len(f) > j and f[j].strip() for f in filas):
            nom, k = f"_extra_{j - ncols + 1}", 1
            while nom in usados:
                k += 1
                nom = f"_extra_{j - ncols + 1}_{k}"
            usados.add(nom)
            extras[j] = nom
    if extras:
        aviso(f"Hay filas con más celdas que columnas en la cabecera; "
              f"se guardan como {', '.join(extras.values())}.")

    cortas = 0
    raiz = ET.Element('incidencies')
    for fila in filas:
        inc = ET.SubElement(raiz, 'incidencia')
        if len(fila) < ncols:
            cortas += 1
        for i, nom in enumerate(nombres):
            valor = fila[i] if i < len(fila) else ''
            ET.SubElement(inc, nom).text = limpiar_texto(valor).strip()
        for j, nom in extras.items():
            valor = fila[j] if j < len(fila) else ''
            ET.SubElement(inc, nom).text = limpiar_texto(valor).strip()
    if cortas:
        aviso(f"{cortas} fila(s) tenían menos celdas que la cabecera; "
              "se han rellenado con valores vacíos.")

    _indentar(raiz)
    return ET.ElementTree(raiz), len(filas), ncols


def escribir_xml(arbol, destino):
    """Escritura atómica: primero a un temporal y luego se renombra, así un fallo
    a medias nunca deja un XML corrupto. Si el destino está bloqueado, usa otro nombre."""
    base, ext = os.path.splitext(destino)
    candidatos = [destino,
                  f"{base}_{datetime.now():%Y%m%d_%H%M%S}{ext}",
                  os.path.join(tempfile.gettempdir(), os.path.basename(destino))]
    ultimo = None
    for cand in candidatos:
        tmp = f"{cand}.{os.getpid()}.tmp"
        try:
            arbol.write(tmp, encoding='utf-8', xml_declaration=True)
            os.replace(tmp, cand)
            if cand != destino:
                aviso(f"No se pudo escribir '{destino}' (¿abierto en otro programa?). "
                      f"XML guardado en '{cand}'.")
            return cand
        except OSError as e:
            ultimo = e
        finally:
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except OSError:
                pass
    raise ErrorConvertidor(f"No se pudo escribir el XML ({ultimo}).\n"
                           "Revisa que haya espacio en disco y permisos de escritura.")


def verificar_xml(ruta, esperadas):
    """Relee el XML escrito y comprueba que es válido y completo."""
    try:
        raiz = ET.parse(ruta).getroot()
    except ET.ParseError as e:
        raise ErrorConvertidor(f"El XML generado no es válido ({e}). Esto no debería pasar.")
    except OSError as e:
        raise ErrorConvertidor(f"No se pudo releer el XML generado: {e}")
    if len(raiz) != esperadas:
        raise ErrorConvertidor(f"El XML tiene {len(raiz)} incidencias pero se esperaban {esperadas}.")


def csv_a_xml(csv_path, xml_path):
    validar_entrada(csv_path)
    if os.path.abspath(csv_path) == os.path.abspath(xml_path):
        raise ErrorConvertidor("El archivo de salida no puede ser el mismo que el CSV de entrada.")

    subir_limite_csv()
    datos = leer_bytes(csv_path)
    texto, codificacion = decodificar(datos)
    delim, texto = detectar_delimitador(texto)

    cabecera, filas = parsear_csv(texto, delim)
    if not cabecera:
        raise ErrorConvertidor("El CSV no tiene cabecera (todas las filas están vacías).")
    if not filas:
        raise ErrorConvertidor("El CSV solo tiene cabecera, no contiene ninguna respuesta.")

    arbol, total, ncols = construir_xml(cabecera, filas)
    if ncols == 0:
        raise ErrorConvertidor("No se ha detectado ninguna columna válida en la cabecera.")

    destino = escribir_xml(arbol, xml_path)
    verificar_xml(destino, total)

    print(f"[OK] XML generado: {destino}")
    print(f"[OK] Número total de datos: {total}")
    return destino


# ----------------------------------------------------------------------------
# Programa principal
# ----------------------------------------------------------------------------
def carpeta_del_script():
    try:
        return os.path.dirname(os.path.abspath(__file__))
    except NameError:
        return os.getcwd()


def main():
    ap = argparse.ArgumentParser(description="Convierte un CSV de incidencias a XML.")
    ap.add_argument('csv', nargs='?', help=f"CSV de entrada (por defecto {NOMBRE_CSV})")
    ap.add_argument('xml', nargs='?', help=f"XML de salida (por defecto {NOMBRE_XML})")
    a = ap.parse_args()

    base = carpeta_del_script()
    if a.csv:
        csv_path = os.path.abspath(a.csv)
        xml_path = os.path.abspath(a.xml) if a.xml else \
            os.path.splitext(csv_path)[0] + '.xml'
    else:
        csv_path = os.path.join(base, NOMBRE_CSV)
        xml_path = os.path.abspath(a.xml) if a.xml else os.path.join(base, NOMBRE_XML)

    csv_a_xml(csv_path, xml_path)
    resumen_avisos()


# ----------------------------------------------------------------------------
# Manejo global de errores
# ----------------------------------------------------------------------------
def describir_error(e):
    if isinstance(e, ET.ParseError):
        return "XML NO VÁLIDO", "El archivo XML está dañado o incompleto."
    if isinstance(e, csv.Error):
        return "CSV MAL FORMADO", "Comillas sin cerrar o celdas demasiado grandes."
    if isinstance(e, UnicodeError):
        return "ERROR DE CODIFICACIÓN", "El archivo tiene caracteres que no se pueden leer."
    if isinstance(e, PermissionError):
        return "SIN PERMISOS", "No se puede leer/escribir el archivo (¿abierto en Excel?)."
    if isinstance(e, FileNotFoundError):
        return "ARCHIVO NO ENCONTRADO", "Ruta incorrecta."
    if isinstance(e, OSError):
        return "ERROR DEL SISTEMA", "Fallo de disco o del sistema operativo."
    if isinstance(e, MemoryError):
        return "SIN MEMORIA", "El archivo es demasiado grande para este equipo."
    if isinstance(e, RecursionError):
        return "RECURSIÓN EXCESIVA", "Bucle interno del programa."
    if isinstance(e, (KeyError, IndexError, TypeError, AttributeError, ValueError)):
        return "DATOS INESPERADOS", "El contenido del archivo no tiene el formato esperado."
    return "ERROR INESPERADO", "Error no previsto en el script."


def escribir_seguro(ruta, texto):
    base, ext = os.path.splitext(ruta)
    for destino in (ruta, f"{base}_{datetime.now():%Y%m%d_%H%M%S}{ext}"):
        try:
            with open(destino, 'w', encoding='utf-8') as fh:
                fh.write(texto)
            return destino
        except OSError:
            continue
    return None


def manejar_excepcion(e):
    """Muestra el error y guarda el traceback completo. No puede fallar."""
    try:
        titulo, causa = describir_error(e)
        tb = traceback.extract_tb(e.__traceback__)
        donde = f"{tb[-1].filename}, línea {tb[-1].lineno}, en {tb[-1].name}()" if tb else ""
        linea = "=" * 60
        print(f"\n{linea}\n❌ NO SE PUDO EJECUTAR EL SCRIPT\n{linea}", file=sys.stderr)
        print(f"Tipo de error : {titulo}", file=sys.stderr)
        print(f"Posible causa : {causa}", file=sys.stderr)
        print(f"Detalle       : {type(e).__name__}: {e}", file=sys.stderr)
        if donde:
            print(f"Dónde         : {donde}", file=sys.stderr)
        print(linea, file=sys.stderr)
        completo = "".join(traceback.format_exception(type(e), e, e.__traceback__))
        guardado = escribir_seguro(ERROR_LOG, f"{datetime.now():%Y-%m-%d %H:%M:%S}\n{completo}")
        if guardado:
            print(f"Traceback completo guardado en: {guardado}", file=sys.stderr)
    except BaseException:
        try:
            print(f"\n❌ ERROR: {type(e).__name__}: {e}", file=sys.stderr)
        except BaseException:
            pass


def pausar():
    try:
        input("\nPulsa Enter para cerrar...")
    except BaseException:
        pass


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n⚠️ Detenido por el usuario (Ctrl+C).", file=sys.stderr)
        sys.exit(130)
    except BrokenPipeError:
        try:
            sys.stdout = open(os.devnull, 'w')
        except OSError:
            pass
        sys.exit(0)
    except ErrorConvertidor as e:
        resumen_avisos()
        for linea in str(e).splitlines():
            print(f"[ERROR] {linea}")
        pausar()
        sys.exit(1)
    except Exception as e:
        manejar_excepcion(e)
        pausar()
        sys.exit(1)