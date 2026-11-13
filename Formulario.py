#!/usr/bin/env python3

import sys

# ----------------------------------------------------------------------------
# Comprobaciones previas: si algo falta, se avisa por pantalla y no se cierra
# la ventana de golpe.
# ----------------------------------------------------------------------------
def _salir_con_aviso(msg):
    linea = "=" * 60
    print(f"\n{linea}\n❌ NO SE PUDO EJECUTAR EL SCRIPT\n{linea}", file=sys.stderr)
    print(msg, file=sys.stderr)
    print(linea, file=sys.stderr)
    try:
        input("\nPulsa Enter para cerrar...")
    except Exception:
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
import csv
import html as htmllib
import json
import os
import random
import re
import string
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta

try:
    import requests
except ImportError:
    _salir_con_aviso("Tipo de error : FALTA UNA LIBRERÍA\n"
                     "Posible causa : No tienes instalada la librería 'requests'.\n"
                     "Solución      : Abre una terminal y ejecuta: pip install requests")

"MODIFICAR EL URL DEL FORMULARIO DE GOOGLE FORMS AQUÍ"

FORM_URL = (
    "https://docs.google.com/forms/d/e/"
    "1FAIpQLSciTjyANABNp8H_mAPsjFAjwEv1DL9BwOKBvNtzIG9ZIHM1ag"
)
OK_MARKER = "freebirdFormviewerViewResponseConfirmationMessage"
DEBUG_FILE = "debug_respuesta.html"
ERROR_LOG = "error_script.log"
MAX_FALLOS_SEGUIDOS = 10
CODIGOS_REINTENTO = (429, 500, 502, 503, 504)

# Tipos de pregunta en los datos internos de Google Forms
T_TEXTO, T_PARRAFO, T_OPCION, T_DESPLEGABLE, T_CASILLAS = 0, 1, 2, 3, 4
T_ESCALA = 5
T_SECCION, T_FECHA = 8, 9
TIPOS_OPCION = (T_OPCION, T_DESPLEGABLE, T_ESCALA)

# Inicio del título de cada pregunta (minúsculas) -> clave interna
CLAVES = {
    "nom": "nom", "cognom": "cognom", "data": "data",
    "quin dispositiu": "dispositiu", "prioritat": "prioritat", "lloc": "lloc",
    "informa": "incidencia", "cuants": "usuaris", "identificador": "equip",
    "comentari": "comentari",
}

# ------------------------------------------------------------- datos falsos
NOMS = ["Marc", "Laia", "Pau", "Júlia", "Arnau", "Marta", "Jordi", "Núria",
        "Pol", "Clara", "Oriol", "Anna", "Biel", "Carla", "Sergi", "Mireia",
        "David", "Sara", "Joan", "Aina", "Àlex", "Emma", "Hugo", "Lucía"]
COGNOMS = ["Garcia", "Martínez", "López", "Sánchez", "Pérez", "Puig", "Soler",
           "Vila", "Ferrer", "Serra", "Roca", "Vidal", "Costa", "Mas",
           "Ribas", "Torres", "Mora", "Sala", "Pons", "Bosch", "Zegarra"]
PALABRAS = ["ordinador", "pantalla", "no", "funciona", "cable", "xarxa", "lent",
            "projector", "teclat", "ratolí", "aula", "error", "bloquejat",
            "reiniciar", "imatge", "so", "connexió", "impressora", "urgent",
            "revisar", "avui", "demà", "setmana", "sense", "senyal", "bateria"]
OTROS_DISP = ["Impressora", "Router", "Pissarra digital", "Altaveus", "Webcam",
              "Tauleta", "Escàner", "Micròfon", "Switch", "SAI"]

# Modo coherente
LLOCS = {"Aula 101": "101", "Aula 102": "102", "Aula 206": "206",
         "Aula 207": "207", "Aula 305": "305", "Laboratori d'informàtica": "LAB",
         "Sala de professors": "PRO", "Biblioteca": "BIB", "Secretaria": "SEC",
         "Taller de robòtica": "TAL", "Sala d'actes": "ACT",
         "Despatx direcció": "DIR"}
USUARIS = ["1", "2-10", "11-20", "21-30", "+30"]
DISPOSITIUS = {
    "Ordinador": (30, "PC", ["L'ordinador no s'encén", "L'ordinador va molt lent",
                             "Pantalla blava en iniciar"], [60, 30, 7, 2, 1]),
    "Monitor": (20, "MON", ["El monitor no mostra imatge",
                            "La pantalla parpelleja"], [70, 25, 4, 1, 0]),
    "Ratolí": (12, "RAT", ["El ratolí no respon",
                           "El botó esquerre no funciona"], [90, 10, 0, 0, 0]),
    "Teclat": (12, "TEC", ["Algunes tecles no funcionen", "Tecles enganxades"],
               [90, 10, 0, 0, 0]),
    "Cables": (8, "CAB", ["Cable HDMI trencat", "Cable de xarxa defectuós"],
               [60, 30, 8, 2, 0]),
    "Projector": (10, "PRJ", ["El projector no s'encén", "Imatge borrosa"],
                  [10, 50, 25, 10, 5]),
}


def fecha_aleatoria(rng, d0, d1):
    return (d0 + timedelta(days=rng.randint(0, max((d1 - d0).days, 0)))).isoformat()


def generar_coherente(campos, rng, d0, d1):
    disp = rng.choices(list(DISPOSITIUS), [v[0] for v in DISPOSITIUS.values()])[0]
    _, pref, descs, pesos = DISPOSITIUS[disp]
    lloc = rng.choice(list(LLOCS))
    return {
        "nom": rng.choice(NOMS),
        "cognom": f"{rng.choice(COGNOMS)} {rng.choice(COGNOMS)}",
        "data": fecha_aleatoria(rng, d0, d1),
        "dispositiu": disp,
        "prioritat": rng.choices(["Baix", "Mitja", "Urgent"], [40, 40, 20])[0],
        "lloc": lloc,
        "incidencia": rng.choice(descs),
        "usuaris": USUARIS[rng.choices(range(5), pesos)[0]],
        "equip": f"{pref}-{LLOCS[lloc]}-{rng.randint(1, 30):02d}",
        "comentari": rng.choice(["", "", "Passa de forma intermitent"]),
    }


def texto_aleatorio(rng, clave):
    if clave == "nom":
        return rng.choice(NOMS)
    if clave == "cognom":
        return f"{rng.choice(COGNOMS)} {rng.choice(COGNOMS)}"
    if clave == "equip":
        letras = "".join(rng.choices(string.ascii_uppercase, k=rng.randint(2, 3)))
        return f"{letras}-{rng.randint(1, 999):03d}-{rng.randint(1, 30):02d}"
    return " ".join(rng.choices(PALABRAS, k=rng.randint(2, 7))).capitalize()


def generar_aleatorio(campos, rng, d0, d1):
    """Un valor al azar por campo (indexado por entry ID), usando las opciones
    reales del formulario. Nada tiene que ser coherente con nada."""
    valores = {}
    for c in campos:
        t = c["tipo"]
        ops = c["opciones"]
        if t == T_FECHA:
            valores[c["entry"]] = fecha_aleatoria(rng, d0, d1)
        elif t in TIPOS_OPCION:
            if c["permite_otro"] and (not ops or rng.random() < 0.15):
                valores[c["entry"]] = rng.choice(OTROS_DISP)
            elif ops:
                valores[c["entry"]] = rng.choice(ops)
            elif c["obligatorio"]:
                valores[c["entry"]] = texto_aleatorio(rng, c["clave"])
            # si no es obligatoria y no hay opciones, se deja vacía
        elif t == T_CASILLAS and ops:
            k = rng.randint(1, min(2, len(ops)))
            valores[c["entry"]] = rng.sample(ops, k)
        else:
            if not c["obligatorio"] and rng.random() < 0.3:
                continue  # algunos campos opcionales se dejan vacíos
            valores[c["entry"]] = texto_aleatorio(rng, c["clave"])
    return valores


# --------------------------------------------------------------- formulario
def normalizar_url(url):
    """Acepta la URL con o sin /viewform, /edit, parámetros, barra final...
    y la deja en la forma base que usa el resto del script."""
    url = (url or "").strip().strip("\"'")
    if not url.startswith(("http://", "https://")):
        raise ValueError("la URL debe empezar por https://")
    if "forms.gle/" in url:  # enlace corto: se resuelve a la URL real
        url = requests.get(url, timeout=20, allow_redirects=True).url
    url = re.sub(r"[?#].*$", "", url)
    url = re.sub(r"/(viewform|formResponse|edit|prefill)/?$", "", url)
    url = url.rstrip("/")
    if "docs.google.com/forms/" not in url:
        raise ValueError("no parece una URL de Google Forms "
                         "(debe contener docs.google.com/forms/...)")
    return url


def get_con_reintentos(url, reintentos=3):
    ultimo = "sin detalle"
    for intento in range(reintentos):
        try:
            r = requests.get(url, timeout=20)
        except (requests.ConnectionError, requests.Timeout) as e:
            ultimo = f"{type(e).__name__}: {e}"
        else:
            if r.status_code not in CODIGOS_REINTENTO:
                return r
            ultimo = f"HTTP {r.status_code}"
        time.sleep(min(2 ** intento, 10))
    raise requests.ConnectionError(
        f"No se pudo cargar el formulario tras {reintentos} intentos ({ultimo})")


def cargar_formulario():
    """Lee las preguntas, entry IDs y opciones del HTML del formulario."""
    r = get_con_reintentos(FORM_URL + "/viewform")
    if r.status_code == 404:
        sys.exit("El formulario no existe (HTTP 404). Revisa FORM_URL.")
    r.raise_for_status()
    if "accounts.google.com" in r.url:
        sys.exit("El formulario exige iniciar sesión con una cuenta de Google.")
    m = re.search(r"FB_PUBLIC_LOAD_DATA_\s*=\s*(.*?);\s*</script>", r.text, re.S)
    if not m:
        sys.exit("No se pudo leer la estructura del formulario "
                 "(¿está cerrado o ha cambiado?).")
    items = json.loads(m.group(1))[1][1] or []
    campos, secciones, omitidos = [], 1, 0
    for it in items:
        try:
            if len(it) > 3 and it[3] == T_SECCION:
                secciones += 1
            if len(it) < 5 or not it[4]:
                continue  # títulos, imágenes, secciones...
            q = it[4][0]
            if q[0] is None:
                continue
            ops = q[1] or []
            titulo = (it[1] or "").strip()
            campos.append({
                "titulo": titulo,
                "clave": next((v for k, v in CLAVES.items()
                               if titulo.lower().startswith(k)), None),
                "tipo": it[3],
                "entry": q[0],
                "obligatorio": bool(q[2]) if len(q) > 2 else False,
                "opciones": [o[0] for o in ops if o and o[0]],
                "permite_otro": any(len(o) > 4 and o[4] for o in ops if o),
            })
        except (IndexError, KeyError, TypeError, AttributeError):
            omitidos += 1  # un elemento raro no debe tumbar todo el script
    if omitidos:
        print(f"Aviso: {omitidos} elemento(s) del formulario no se pudieron "
              "leer y se han omitido.", file=sys.stderr)
    if not campos:
        sys.exit("No se detectó ninguna pregunta en el formulario "
                 "(¿URL equivocada o estructura cambiada?).")
    return campos, secciones


def construir_payload(campos, valores, secciones):
    payload = {}
    for c in campos:
        v = valores.get(c["entry"], valores.get(c["clave"]))
        if v in (None, "", []):
            if c["obligatorio"]:
                raise ValueError(
                    f"Campo obligatorio sin valor: '{c['titulo']}' "
                    "(¿pregunta nueva que el script no conoce? usa --modo aleatorio)")
            continue
        eid = f"entry.{c['entry']}"
        if c["tipo"] == T_FECHA:
            try:
                d = datetime.strptime(str(v), "%Y-%m-%d")
            except ValueError:
                raise ValueError(f"Fecha '{v}' no válida para '{c['titulo']}' "
                                 "(formato AAAA-MM-DD)")
            payload.update({f"{eid}_year": d.year, f"{eid}_month": d.month,
                            f"{eid}_day": d.day})
        elif c["tipo"] in TIPOS_OPCION:
            v = str(v)
            match = next((o for o in c["opciones"] if str(o).lower() == v.lower()), None)
            if match:
                payload[eid] = match
            elif c["permite_otro"]:
                payload[eid] = "__other_option__"
                payload[f"{eid}.other_option_response"] = v
            else:
                raise ValueError(f"'{v}' no válido para '{c['titulo']}'. "
                                 f"Opciones: {', '.join(map(str, c['opciones']))}")
        else:
            payload[eid] = v
    payload["pageHistory"] = ",".join(str(i) for i in range(secciones))
    payload["fvv"] = "1"
    return payload


# -------------------------------------------------------------------- envío
_local = threading.local()
_debug_lock = threading.Lock()


def sesion():
    if not hasattr(_local, "s"):
        _local.s = requests.Session()
    return _local.s


def escribir_seguro(ruta, texto):
    """Escribe un archivo sin tumbar el script si no se puede (p. ej. abierto
    en Excel). Devuelve la ruta realmente usada o None."""
    base, ext = os.path.splitext(ruta)
    candidatos = [ruta, f"{base}_{datetime.now():%Y%m%d_%H%M%S}{ext}"]
    for destino in candidatos:
        try:
            with open(destino, "w", encoding="utf-8", newline="") as fh:
                fh.write(texto)
            return destino
        except OSError:
            continue
    return None


def extraer_errores(texto):
    errores = re.findall(r'role="alert"[^>]*>(.*?)</', texto, re.S)
    errores += re.findall(r'ItemErrorMessage[^>]*>(.*?)</', texto, re.S)
    limpios = [htmllib.unescape(re.sub(r"<[^>]+>", "", e)).strip() for e in errores]
    return sorted({e for e in limpios if e})


def evaluar(r):
    """Clasifica la respuesta de Google: ('ok'|'rechazada'|'reintentar'|'error', detalle)."""
    t = r.text
    if r.status_code in CODIGOS_REINTENTO:
        return "reintentar", f"HTTP {r.status_code}"
    if r.status_code != 200:
        return "error", f"HTTP {r.status_code}"
    if OK_MARKER in t:
        return "ok", "ok"
    if "accounts.google.com" in r.url:
        return "error", "El formulario exige iniciar sesión con cuenta de Google"
    low = t.lower()
    if any(s in low for s in ("no longer accepting", "ja no accepta",
                              "ya no acepta", "deixat d'acceptar")):
        return "error", "El formulario ya no acepta respuestas"
    errores = extraer_errores(t)
    if errores:
        return "rechazada", " | ".join(errores)
    if 'name="entry.' in t:
        return "rechazada", "Google devolvió el formulario de nuevo (campos no aceptados)"
    # 200 sin error y sin el formulario de vuelta: es la página de confirmación
    return "ok", "ok"


def enviar(payload, delay, reintentos=4):
    """Devuelve (estado, detalle). Estados: ok, rechazada, error, incierta.
    Solo reintenta cuando Google seguro NO procesó la petición (429/5xx o fallo
    de conexión); un timeout de lectura puede haber llegado, así que no se reenvía.
    Nunca lanza excepciones: cualquier fallo se convierte en un estado."""
    detalle = "agotados los reintentos"
    for intento in range(reintentos):
        try:
            r = sesion().post(FORM_URL + "/formResponse", data=payload, timeout=20)
        except (requests.ConnectionError, requests.ConnectTimeout) as e:
            detalle = f"conexión: {e}"
            time.sleep(min(2 ** intento, 20))
            continue
        except requests.RequestException as e:
            return "incierta", f"sin respuesta (puede haber llegado): {e}"
        except Exception as e:
            return "error", f"{type(e).__name__}: {e}"
        try:
            estado, det = evaluar(r)
        except Exception as e:
            return "incierta", f"respuesta ilegible ({type(e).__name__}: {e})"
        if estado == "ok":
            time.sleep(delay)
            return "ok", det
        if estado == "reintentar":
            detalle = det
            time.sleep(min(2 ** intento + random.random(), 20))
            continue
        try:
            with _debug_lock:
                escribir_seguro(DEBUG_FILE, r.text)
        except Exception:
            pass
        return estado, det
    return "error", detalle


def preguntar(texto, defecto=None):
    try:
        resp = input(texto).strip()
    except (EOFError, RuntimeError):
        resp = ""
    return resp or defecto


def guardar_log(ruta, payloads, estados, detalles):
    """Guarda el CSV de resultados. Si el archivo está bloqueado (Excel),
    usa otro nombre; si tampoco se puede, avisa pero no rompe el script."""
    base, ext = os.path.splitext(ruta)
    candidatos = [ruta, f"{base}_{datetime.now():%Y%m%d_%H%M%S}{ext}"]
    for destino in candidatos:
        try:
            with open(destino, "w", newline="", encoding="utf-8") as fh:
                w = csv.writer(fh)
                w.writerow(["n", "estado", "detalle", "payload"])
                for i, pl in enumerate(payloads):
                    w.writerow([i + 1, estados[i], detalles[i],
                                json.dumps(pl, ensure_ascii=False, default=str)])
            if destino != ruta:
                print(f"Aviso: no se pudo escribir '{ruta}' (¿abierto en Excel?). "
                      f"Log guardado en '{destino}'.", file=sys.stderr)
            return destino
        except OSError:
            continue
    print(f"Aviso: NO se pudo guardar el log en '{ruta}' ni en una alternativa.",
          file=sys.stderr)
    return None


def main():
    global FORM_URL
    p = argparse.ArgumentParser(description="Envío masivo al formulario de incidencias.")
    p.add_argument("--listar", action="store_true",
                   help="muestra los campos detectados y sale")
    p.add_argument("--n", type=int, help="número de respuestas (si no, lo pregunta)")
    p.add_argument("--modo", choices=["aleatorio", "coherente"], default="aleatorio")
    p.add_argument("--workers", type=int, default=3, help="hilos en paralelo (2-5)")
    p.add_argument("--delay", type=float, default=0.5, help="pausa (s) tras cada envío")
    p.add_argument("--desde", default=(date.today() - timedelta(days=60)).isoformat(),
                   help="fecha mínima AAAA-MM-DD (por defecto, hace 60 días)")
    p.add_argument("--hasta", default=date.today().isoformat(),
                   help="fecha máxima AAAA-MM-DD (por defecto, hoy)")
    p.add_argument("--seed", type=int, help="semilla para resultados reproducibles")
    p.add_argument("--log", default="enviadas.csv", help="CSV con el estado de cada envío")
    p.add_argument("--dry-run", action="store_true", help="no envía, solo muestra")
    p.add_argument("--yes", action="store_true", help="no pide confirmaciones")
    a = p.parse_args()

    # ---- Validación de argumentos (antes de tocar la red) ----
    if not 1 <= a.workers <= 5:
        nuevo = max(1, min(a.workers, 5))
        print(f"Aviso: --workers={a.workers} fuera de rango, se usará {nuevo}.",
              file=sys.stderr)
        a.workers = nuevo
    if a.delay < 0:
        print("Aviso: --delay negativo, se usará 0.", file=sys.stderr)
        a.delay = 0.0
    if a.n is not None and a.n < 1:
        sys.exit("El número de respuestas (--n) debe ser al menos 1.")
    try:
        d0 = datetime.strptime(a.desde, "%Y-%m-%d").date()
        d1 = datetime.strptime(a.hasta, "%Y-%m-%d").date()
    except ValueError:
        sys.exit(f"Fecha no válida en --desde ('{a.desde}') o --hasta ('{a.hasta}'). "
                 "Usa el formato AAAA-MM-DD, por ejemplo 2025-03-31.")
    if d0 > d1:
        sys.exit(f"--desde ({a.desde}) no puede ser posterior a --hasta ({a.hasta}).")
    try:
        FORM_URL = normalizar_url(FORM_URL)
    except ValueError as e:
        sys.exit(f"FORM_URL no válida: {e}")

    print("Formulario:", FORM_URL)
    campos, secciones = cargar_formulario()

    if a.listar:
        print(f"Secciones: {secciones}")
        for c in campos:
            print(f"{'OK ' if c['clave'] else '?? '}entry.{c['entry']:<12} "
                  f"{'*' if c['obligatorio'] else ' '} tipo={c['tipo']}  {c['titulo']}")
            if c["opciones"]:
                print(f"{'':20}opciones: {', '.join(map(str, c['opciones']))}"
                      f"{' + Other' if c['permite_otro'] else ''}")
        return

    if a.n is None:
        txt = preguntar("¿Cuántas respuestas quieres enviar? [400]: ", "400")
        try:
            a.n = int(txt)
        except ValueError:
            sys.exit(f"'{txt}' no es un número válido.")
    if a.n < 1:
        sys.exit("El número de respuestas debe ser al menos 1.")

    rng = random.Random(a.seed)
    gen = generar_aleatorio if a.modo == "aleatorio" else generar_coherente

    filas = [gen(campos, rng, d0, d1) for _ in range(a.n)]
    try:
        payloads = [construir_payload(campos, f, secciones) for f in filas]
    except ValueError as e:
        sys.exit(f"Error: {e}")

    if a.dry_run:
        for pl in payloads[:3]:
            print(json.dumps(pl, ensure_ascii=False))
        print(f"\n(dry-run) {a.n} respuestas generadas, no se ha enviado nada.")
        return

    if not a.yes:
        if preguntar(f"Se enviarán {a.n} respuestas al formulario. ¿Continuar? (s/n): ",
                     "n").lower() not in ("s", "si", "sí", "y", "yes"):
            sys.exit("Cancelado.")

    estados = ["pendiente"] * a.n
    detalles = [""] * a.n

    # 1) Envío de prueba
    est, det = enviar(payloads[0], a.delay)
    estados[0], detalles[0] = est, det
    if est != "ok":
        print(f"\nEl envío de prueba NO se ha confirmado ({est}): {det}")
        if os.path.exists(DEBUG_FILE):
            print(f"Respuesta de Google guardada en {DEBUG_FILE}.")
        print("No se lanza el masivo.")
        guardar_log(a.log, payloads, estados, detalles)
        sys.exit(1)
    print("\nEnvío de prueba aceptado por Google.")
    if not a.yes:
        print("Abre el formulario > pestaña Respuestas y comprueba que ha subido en 1.")
        if preguntar("¿Ha subido el contador? (s/n): ", "n").lower() not in (
                "s", "si", "sí", "y", "yes"):
            print("Entonces el script no detecta bien las respuestas. "
                  f"Revisa {DEBUG_FILE} y pásamelo.")
            guardar_log(a.log, payloads, estados, detalles)
            sys.exit(1)

    # 2) Envío del resto
    parar = threading.Event()
    lock = threading.Lock()
    seguidos = {"n": 0}

    def tarea(i):
        if parar.is_set():
            return i, "cancelada", "abortado"
        try:
            est, det = enviar(payloads[i], a.delay)
        except Exception as e:  # red de seguridad: un hilo nunca debe romper el resto
            est, det = "error", f"{type(e).__name__}: {e}"
        with lock:
            if est == "ok":
                seguidos["n"] = 0
            else:
                seguidos["n"] += 1
                if seguidos["n"] >= MAX_FALLOS_SEGUIDOS:
                    parar.set()
        return i, est, det

    t0 = time.time()
    hechos = 1
    interrumpido = False
    ex = ThreadPoolExecutor(max_workers=a.workers)
    futs = {}
    try:
        futs = {ex.submit(tarea, i): i for i in range(1, a.n)}
        for fut in as_completed(futs):
            try:
                i, est, det = fut.result()
            except Exception as e:
                i, est, det = futs[fut], "error", f"{type(e).__name__}: {e}"
            estados[i], detalles[i] = est, det
            hechos += 1
            if hechos % 20 == 0 or hechos == a.n:
                ok = estados.count("ok")
                print(f"[{hechos}/{a.n}] ok={ok} "
                      f"fallidas={sum(e in ('rechazada', 'error') for e in estados)} "
                      f"inciertas={estados.count('incierta')} "
                      f"({time.time() - t0:.0f}s)")
    except KeyboardInterrupt:
        interrumpido = True
        parar.set()
        print("\n⚠️ Interrumpido: esperando a que terminen los envíos en curso...",
              file=sys.stderr)
    finally:
        for f in futs:
            f.cancel()
        ex.shutdown(wait=True)
        guardar_log(a.log, payloads, estados, detalles)

    ok = estados.count("ok")
    mal = sum(e in ("rechazada", "error") for e in estados)
    inc = estados.count("incierta")
    canc = estados.count("cancelada") + estados.count("pendiente")
    print(f"\nTerminado: {ok}/{a.n} enviadas en {time.time() - t0:.0f}s. Log: {a.log}")
    if inc:
        print(f"{inc} inciertas: no hubo respuesta de Google y pueden haber llegado. "
              "No se reenvían para evitar duplicados; compara con el contador del formulario.")
    if canc:
        print(f"{canc} canceladas: se abortó "
              f"{'por interrupción del usuario' if interrumpido else f'tras {MAX_FALLOS_SEGUIDOS} fallos seguidos'}.")
    if mal:
        ejemplo = next((d for e, d in zip(estados, detalles)
                        if e in ("rechazada", "error")), "sin detalle")
        print(f"{mal} fallidas, por ejemplo: {ejemplo}")
    if interrumpido:
        raise KeyboardInterrupt
    if mal or inc or canc:
        sys.exit(1)


# ============================================================================
# MANEJO DE ERRORES: cualquier fallo se muestra por pantalla con su tipo
# ============================================================================
def describir_error(e):
    """Devuelve (tipo legible, posible causa) según la excepción."""
    if isinstance(e, requests.exceptions.ConnectTimeout):
        return "TIMEOUT DE CONEXIÓN", "Google no respondió a tiempo. Revisa tu internet."
    if isinstance(e, requests.exceptions.ReadTimeout):
        return "TIMEOUT DE LECTURA", "Google tardó demasiado en responder."
    if isinstance(e, requests.exceptions.SSLError):
        return "ERROR SSL", "Fallo de certificado: revisa la hora del PC, el antivirus o el proxy."
    if isinstance(e, requests.exceptions.ProxyError):
        return "ERROR DE PROXY", "Hay un proxy configurado que no funciona."
    if isinstance(e, requests.exceptions.ConnectionError):
        return "ERROR DE CONEXIÓN", "No hay internet, DNS caído o bloqueo de red/firewall."
    if isinstance(e, requests.exceptions.HTTPError):
        return "ERROR HTTP", "Google devolvió un error (¿URL del formulario mal puesta o formulario borrado?)."
    if isinstance(e, (requests.exceptions.MissingSchema, requests.exceptions.InvalidSchema,
                      requests.exceptions.InvalidURL)):
        return "URL INVÁLIDA", "La FORM_URL no es correcta (debe empezar por https://)."
    if isinstance(e, requests.exceptions.RequestException):
        return "ERROR DE REQUESTS", "Fallo de red al hablar con Google."
    if isinstance(e, json.JSONDecodeError):
        return "ERROR LEYENDO EL FORMULARIO (JSON)", "Google cambió la estructura del formulario o la URL no es de un formulario."
    if isinstance(e, (KeyError, IndexError, TypeError, AttributeError)):
        return "ESTRUCTURA DEL FORMULARIO NO RECONOCIDA", "El formulario tiene un formato distinto al que espera el script."
    if isinstance(e, UnicodeError):
        return "ERROR DE CODIFICACIÓN", "Un texto tiene caracteres que no se pueden procesar."
    if isinstance(e, ValueError):
        return "VALOR NO VÁLIDO", "Un número, fecha (AAAA-MM-DD) u opción es incorrecto."
    if isinstance(e, PermissionError):
        return "SIN PERMISOS", "No se puede escribir el log/debug (¿tienes el CSV abierto en Excel?)."
    if isinstance(e, FileNotFoundError):
        return "ARCHIVO NO ENCONTRADO", "Ruta incorrecta."
    if isinstance(e, OSError):
        return "ERROR DEL SISTEMA", "Fallo de disco o de red a nivel del sistema operativo."
    if isinstance(e, ImportError):
        return "FALTA UNA LIBRERÍA", "Instálala con: pip install requests"
    if isinstance(e, MemoryError):
        return "SIN MEMORIA", "Reduce el número de respuestas (--n)."
    if isinstance(e, RecursionError):
        return "RECURSIÓN EXCESIVA", "Bucle interno del programa."
    return "ERROR INESPERADO", "Error no previsto en el script."


def mostrar_error(titulo, causa, detalle, donde=""):
    linea = "=" * 60
    print(f"\n{linea}\n❌ NO SE PUDO EJECUTAR EL SCRIPT\n{linea}", file=sys.stderr)
    print(f"Tipo de error : {titulo}", file=sys.stderr)
    print(f"Posible causa : {causa}", file=sys.stderr)
    print(f"Detalle       : {detalle}", file=sys.stderr)
    if donde:
        print(f"Dónde         : {donde}", file=sys.stderr)
    print(linea, file=sys.stderr)


def pausar():
    try:
        input("\nPulsa Enter para cerrar...")
    except BaseException:
        pass


def manejar_excepcion(e):
    """Muestra el error y guarda el traceback completo. No puede fallar."""
    try:
        titulo, causa = describir_error(e)
        tb = traceback.extract_tb(e.__traceback__)
        donde = f"{tb[-1].filename}, línea {tb[-1].lineno}, en {tb[-1].name}()" if tb else ""
        mostrar_error(titulo, causa, f"{type(e).__name__}: {e}", donde)
        completo = "".join(traceback.format_exception(type(e), e, e.__traceback__))
        guardado = escribir_seguro(ERROR_LOG, f"{datetime.now():%Y-%m-%d %H:%M:%S}\n{completo}")
        if guardado:
            print(f"Traceback completo guardado en: {guardado}", file=sys.stderr)
    except BaseException:
        # Último recurso: que al menos algo salga por pantalla
        try:
            print(f"\n❌ ERROR: {type(e).__name__}: {e}", file=sys.stderr)
        except BaseException:
            pass


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n⚠️ Detenido por el usuario (Ctrl+C).", file=sys.stderr)
        sys.exit(130)
    except SystemExit as e:
        # sys.exit("mensaje") -> es un error con texto; sys.exit(1) -> fallo ya explicado
        if isinstance(e.code, str):
            mostrar_error("ERROR CONTROLADO", "El script se detuvo a propósito.", e.code)
            pausar()
            sys.exit(1)
        if e.code not in (None, 0):
            pausar()
        raise
    except Exception as e:
        manejar_excepcion(e)
        pausar()
        sys.exit(1)