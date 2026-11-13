#!/usr/bin/env python3
"""
Processa incidencies.xml, mostra estadístiques per pantalla i genera un informe HTML.

Ús:
  python3 ProcessarIncidencies.py                  # llegeix incidencies.xml
  python3 ProcessarIncidencies.py altre.xml
  python3 ProcessarIncidencies.py --no-color       # sense colors al terminal
  python3 ProcessarIncidencies.py --html=sortida.html   # nom de l'informe HTML
  python3 ProcessarIncidencies.py --no-obrir       # no obre l'informe al navegador
  python3 ProcessarIncidencies.py --json-mode=afegir         # si el JSON ja existeix, no pregunta
  python3 ProcessarIncidencies.py --json-mode=sobreescriure
  python3 ProcessarIncidencies.py --json=altre.json          # nom del fitxer JSON
  python3 ProcessarIncidencies.py --debug          # en cas d'error inesperat, mostra el traceback

Passos:
  1. Llegir l'XML (cada fill de l'arrel és una incidència).
  2. Detectar quin camp és la data, el dispositiu, la prioritat...
  3. Netejar i filtrar les dades errònies (dates futures, buides, llocs invàlids, duplicats...).
  4. CÀLCUL: calcular totes les estadístiques en un diccionari.
  5. PRESENTACIÓ: mostrar-les pel terminal i escriure-les en un informe HTML.
  6. Desar les incidències vàlides (amb un ID) i un resum a incidencies.json.
"""
import errno
import functools
import hashlib
import html
import json
import math
import os
import re
import stat
import tempfile
import sys
import unicodedata
import webbrowser
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta
from pathlib import Path

FITXER = "incidencies.xml"
FITXER_HTML = "informe_incidencies.html"
FITXER_JSON = "incidencies.json"
MODES_JSON = ("sobreescriure", "afegir")

# Si la detecció automàtica s'equivoca, posa aquí el nom de l'etiqueta XML correcta.
# Exemple: CAMPS = {"data": "Data_de_lincidència", "dispositiu": "Quin_dispositiu_afecta"}
CAMPS = {}

# Una incidència no pot ser posterior al moment en què s'envia el formulari
# ni més antiga que aquest nombre de dies abans de l'enviament.
MAX_ANTIGUITAT = timedelta(days=365)
# Límit absolut, per si la marca temporal també és absurda (p. ex. any 0001).
DATA_MINIMA = date(2000, 1, 1)

# Valors de lloc que no identifiquen cap espai real (comparats sense accents ni majúscules).
LLOCS_INVALIDS = {"aqui", "alla", "casa", "no ho se", "no se", "-", "?"}
MAX_LLARGADA_LLOC = 40


# ---------------------------------------------------------------------------
# 1. Lectura de l'XML
# ---------------------------------------------------------------------------
def norm(text):
    """Minúscules, sense accents i amb els espais unificats (per comparar valors)."""
    return _norm(str(text))


@functools.lru_cache(maxsize=65536)   # els mateixos valors es repeteixen milers de vegades
def _norm(text):
    text = unicodedata.normalize("NFD", text.lower())
    text = "".join(c for c in text if unicodedata.category(c) != "Mn")
    return " ".join(text.split())


def descriure_error(e, ruta):
    """Missatge en català per a un error de fitxer (OSError)."""
    motius = {
        errno.ENOENT: "no existeix (ni el fitxer ni la carpeta)",
        errno.EACCES: "no tens permís per accedir-hi",
        errno.EPERM: "no tens permís per accedir-hi",
        errno.EROFS: "és en un sistema de fitxers de només lectura",
        errno.EISDIR: "és una carpeta, no un fitxer",
        errno.ENOTDIR: "una part de la ruta no és una carpeta",
        errno.ENOSPC: "no queda espai al disc",
    }
    return f"{ruta}: {motius.get(e.errno, e.strerror or str(e))}"


def netejar(text):
    """Treu espais sobrants (inclosos salts de línia i espais dobles)."""
    return " ".join((text or "").split())


def llegir_xml(fitxer):
    try:
        arrel = ET.parse(fitxer).getroot()
    except FileNotFoundError:
        sys.exit(f"No trobo el fitxer {fitxer}. Executa el programa a la mateixa carpeta.")
    except OSError as e:
        sys.exit(f"No es pot llegir l'XML. {descriure_error(e, fitxer)}.")
    except ET.ParseError as e:
        if os.path.getsize(fitxer) == 0:
            sys.exit(f"El fitxer {fitxer} està buit.")
        sys.exit(f"{fitxer} no és un XML vàlid ({e}).")

    elements = list(arrel)
    # Per si hi ha un nivell intermedi (<arrel><llista><incidencia>...)
    if len(elements) == 1 and len(elements[0]) > 1 and len(elements[0][0]) > 0:
        elements = list(elements[0])

    registres, etiquetes = [], []
    for e in elements:
        r = {k: netejar(v) for k, v in e.attrib.items()}
        for camp in e:
            r[camp.tag] = netejar(camp.text)
        for k in r:
            if k not in etiquetes:
                etiquetes.append(k)
        registres.append(r)
    return registres, etiquetes


# ---------------------------------------------------------------------------
# 2. Detecció dels camps
# ---------------------------------------------------------------------------
# (rol, paraules clau, paraules que l'exclouen)
# Cada paraula es compara amb l'inici de cada "paraula" de l'etiqueta
# (Data_de_lincidència -> data, de, lincidencia), així "dia" no coincideix amb "multimedia".
# Les claus amb "_" es busquen dins l'etiqueta sencera.
# L'ordre importa: el primer rol que reclama una etiqueta se la queda.
PARAULES = [
    ("timestamp", ["marca_de_temps", "marca_temporal", "timestamp"], []),
    ("data", ["data", "fecha", "dia"], ["marca"]),
    ("dispositiu", ["dispositiu", "dispositivo", "aparell", "equip", "tipus"], ["identificador", "codi", "num"]),
    ("prioritat", ["priorit", "urgenc"], []),
    ("lloc", ["lloc", "ubicacio", "aula", "lugar", "espai"], []),
    ("usuaris", ["afectat", "afectad"], ["dispositiu"]),
    ("correu", ["correu", "email", "mail", "usuari", "usuario"], []),
    ("cognom", ["cognom", "apellido"], []),
    ("informador", ["nom", "nombre", "informador", "reporta"], ["usuari", "usuario", "cognom"]),
    ("identificador", ["identificador", "codi", "serie"], []),
]


def coincideix(etiqueta, claus):
    n = norm(etiqueta)
    paraules = re.split(r"[^a-z0-9]+", n)
    for k in claus:
        if "_" in k:
            if k in n:
                return True
        elif any(p.startswith(k) for p in paraules):
            return True
    return False


def detectar_camps(etiquetes):
    rols, usades = {}, set()
    for rol, claus, exclou in PARAULES:
        if rol in CAMPS:
            rols[rol] = CAMPS[rol]
            usades.add(CAMPS[rol])
            continue
        for et in etiquetes:
            if et in usades or et == "id":
                continue
            if coincideix(et, claus) and not coincideix(et, exclou):
                rols[rol] = et
                usades.add(et)
                break
    return rols


# ---------------------------------------------------------------------------
# 3. Neteja i filtratge de dades errònies
# ---------------------------------------------------------------------------
# AAAA-MM-DD, AAAA/MM/DD, DD/MM/AAAA, DD-MM-AAAA o DD/MM/AA, amb text opcional al darrere
# (hora, "a. m. CET"...). Llegir-ho amb una expressió regular és molt més ràpid que
# provar strptime amb cada format (important amb milers d'incidències).
PATRO_DATA = re.compile(r"(\d{1,4})([/-])(\d{1,2})\2(\d{1,4})(?:[\sT].*)?$", re.DOTALL)


@functools.lru_cache(maxsize=65536)
def llegir_data(text):
    """Retorna un objecte date, o None si el text no és una data possible (p. ex. 31/02/2026)."""
    m = PATRO_DATA.match((text or "").strip())
    if not m:
        return None
    a, sep, b, c = m.groups()
    if len(a) == 4:                       # AAAA-MM-DD
        any_, mes, dia = int(a), int(b), int(c)
    elif len(a) <= 2 and len(c) == 4:     # DD/MM/AAAA
        dia, mes, any_ = int(a), int(b), int(c)
    elif len(a) <= 2 and len(c) == 2 and sep == "/":   # DD/MM/AA (com %y: 69-99 -> 19xx)
        dia, mes, any_ = int(a), int(b), int(c)
        any_ += 1900 if any_ >= 69 else 2000
    else:
        return None
    try:
        return date(any_, mes, dia)
    except ValueError:                    # 31/02, mes 13, any 0...
        return None


def unificar_variants(registres, camp):
    """'impressora' i 'Impressora' -> la variant més freqüent ('Impressora')."""
    variants = defaultdict(Counter)
    for r in registres:
        if r.get(camp):
            variants[norm(r[camp])][r[camp]] += 1
    canonic = {k: c.most_common(1)[0][0] for k, c in variants.items()}
    for r in registres:
        if r.get(camp):
            r[camp] = canonic[norm(r[camp])]


def lloc_valid(valor):
    n = norm(valor)
    if not n or n in LLOCS_INVALIDS or len(n) > MAX_LLARGADA_LLOC:
        return False
    if re.fullmatch(r"id-?\d+", n):          # un identificador, no un lloc
        return False
    if re.search(r"(^|\s)-\d", n):           # números negatius ("aula -120323")
        return False
    return True


def preparar(registres, rols):
    """Normalitza els camps categòrics i crea camps derivats (comencen per '_')."""
    for rol in ("dispositiu", "prioritat", "lloc"):
        if rol in rols:
            unificar_variants(registres, rols[rol])
    if "informador" in rols:
        for r in registres:
            parts = [r.get(rols["informador"], ""), r.get(rols.get("cognom"), "")]
            r["_informador"] = " ".join(p for p in parts if p)
        unificar_variants(registres, "_informador")


def filtrar(registres, rols):
    avui = date.today()
    camp_data = rols.get("data") or rols.get("timestamp")
    camp_ts = rols.get("timestamp") if rols.get("data") else None
    ignorar = {"id", rols.get("timestamp")}  # no compten per detectar duplicats
    valides, motius, vistos = [], Counter(), set()

    for r in registres:
        if camp_data:
            d = llegir_data(r.get(camp_data))
            if d is None:
                motius["Data buida o amb format incorrecte"] += 1
                continue
            enviament = (llegir_data(r.get(camp_ts)) if camp_ts else None) or avui
            if d > avui:
                motius["Data futura"] += 1
                continue
            if d > enviament:
                motius["Data posterior a l'enviament"] += 1
                continue
            try:
                limit = enviament - MAX_ANTIGUITAT
            except OverflowError:         # enviament a l'any 1: no hi ha límit inferior possible
                limit = date.min
            if d < DATA_MINIMA:
                motius[f"Data anterior a {DATA_MINIMA.year}"] += 1
                continue
            if d < limit:
                motius[f"Data de més de {MAX_ANTIGUITAT.days} dies abans"] += 1
                continue
            r["_data"] = d
        if "dispositiu" in rols and not r.get(rols["dispositiu"]):
            motius["Sense dispositiu indicat"] += 1
            continue
        if "lloc" in rols and not lloc_valid(r.get(rols["lloc"])):
            motius["Lloc buit o invàlid"] += 1
            continue
        clau = tuple(sorted((k, norm(v)) for k, v in r.items()
                            if k not in ignorar and not k.startswith("_")))
        if clau in vistos:
            motius["Duplicada"] += 1
            continue
        vistos.add(clau)
        r["_id"] = id_incidencia(r, clau)
        valides.append(r)
    return valides, motius


def id_incidencia(r, clau):
    """ID estable de la incidència.

    Si l'XML porta l'atribut "id", es fa servir tal qual. Si no, es calcula una
    empremta (SHA-1) del mateix contingut normalitzat que serveix per detectar
    duplicats (tots els camps menys la marca temporal). Així:
      - el mateix XML processat dues vegades dona els mateixos IDs (mode Afegir no repeteix res);
      - no depèn de la posició al fitxer (si s'afegeixen files a l'XML, els IDs no canvien);
      - és coherent amb el filtre de duplicats: dues incidències amb el mateix ID
        serien també duplicades.
    """
    if r.get("id"):
        return str(r["id"])
    empremta = hashlib.sha1(json.dumps(clau, ensure_ascii=False).encode("utf-8")).hexdigest()
    return "INC-" + empremta[:12]


# ---------------------------------------------------------------------------
# 4. CÀLCUL de les estadístiques (sense imprimir res)
# ---------------------------------------------------------------------------
MESOS = ["gen", "feb", "mar", "abr", "maig", "juny", "jul", "ag", "set", "oct", "nov", "des"]
DIES = ["Dilluns", "Dimarts", "Dimecres", "Dijous", "Divendres", "Dissabte", "Diumenge"]
ORDRE_PRIORITAT = ["baix", "mitj", "medi", "normal", "alt", "urgen", "crit"]


def pes_prioritat(valor):
    n = norm(valor)
    return next((i for i, k in enumerate(ORDRE_PRIORITAT) if k in n), 99)


def nivell_prioritat(valor):
    """'alta', 'mitja' o 'baixa': el fan servir el terminal (colors) i l'HTML (classes CSS)."""
    n = norm(valor)
    if any(k in n for k in ("crit", "urgen", "alt")):
        return "alta"
    if any(k in n for k in ("mitj", "medi", "normal")):
        return "mitja"
    return "baixa"


def valor(r, camp):
    return r.get(camp, "") or "(buit)"


def comptar(registres, camp):
    return Counter(valor(r, camp) for r in registres)


def calcular_estadistiques(fitxer, registres, etiquetes, rols, valides, motius, amb_descarts=True):
    """Retorna un diccionari amb TOTES les dades de l'informe.

    Les distribucions són llistes de (etiqueta, quantitat). Una secció val None si
    el camp corresponent no s'ha trobat a l'XML.
    amb_descarts=False omet la conclusió sobre registres descartats (per al JSON,
    on totes les incidències ja són vàlides).
    """
    total, n_val = len(registres), len(valides)
    res = {
        "fitxer": fitxer,
        "data_informe": date.today(),
        "camps": [(rol, rols.get(rol)) for rol, _, _ in PARAULES],
        "qualitat": {
            "total": total,
            "valides": n_val,
            "descartades": total - n_val,
            "motius": motius.most_common(),
        },
        "dispositius": None, "prioritats": None, "llocs": None, "usuaris": None,
        "mensual": None, "dies_setmana": None, "creuada": None, "informadors": None,
        "altres": [], "conclusions": [],
    }
    if not n_val:
        return res

    if "dispositiu" in rols:
        res["dispositius"] = comptar(valides, rols["dispositiu"]).most_common()

    if "prioritat" in rols:
        res["prioritats"] = sorted(comptar(valides, rols["prioritat"]).items(),
                                   key=lambda x: pes_prioritat(x[0]))

    if "lloc" in rols:
        res["llocs"] = comptar(valides, rols["lloc"]).most_common(10)

    if "usuaris" in rols:
        def num_inicial(v):  # "2-5" -> 2, "+30" -> 30 (per ordenar els rangs)
            m = re.search(r"\d+", v[0])
            return (int(m.group()) if m else 9999, v[0].startswith("+"))
        res["usuaris"] = sorted(comptar(valides, rols["usuaris"]).items(), key=num_inicial)

    te_data = all("_data" in r for r in valides)
    if te_data:
        mesos = Counter((r["_data"].year, r["_data"].month) for r in valides)
        res["mensual"] = [(f"{MESOS[m - 1]} {a}", mesos[(a, m)]) for a, m in sorted(mesos)]
        dies = Counter(r["_data"].weekday() for r in valides)
        res["dies_setmana"] = [(DIES[d], dies[d]) for d in range(7)]

    if "dispositiu" in rols and "prioritat" in rols:
        cf, cc = rols["dispositiu"], rols["prioritat"]
        files = [f for f, _ in res["dispositius"]]
        cols = [c for c, _ in res["prioritats"]]
        creuat = Counter((valor(r, cf), valor(r, cc)) for r in valides)
        res["creuada"] = {
            "files": files,
            "columnes": cols,
            "valors": {f: [creuat[(f, c)] for c in cols] for f in files},
        }

    if "informador" in rols:
        res["informadors"] = comptar(valides, "_informador").most_common(5)

    # Altres camps amb pocs valors diferents (es mostren automàticament)
    for et in etiquetes:
        if et in rols.values() or et == "id":
            continue
        c = comptar(valides, et)
        if 1 < len(c) <= 12:
            res["altres"].append((et, c.most_common()))

    # Conclusions: (text abans, text destacat, text després, és alerta?)
    conc = res["conclusions"]
    if res["dispositius"]:
        d, n = res["dispositius"][0]
        conc.append(("El dispositiu més problemàtic és ", d,
                     f" ({n / n_val * 100:.1f}% de les incidències).", False))
    if res["llocs"]:
        l, n = res["llocs"][0]
        conc.append(("El lloc amb més incidències és ", l, f" ({n} incidències).", False))
    if res["prioritats"]:
        altes = [(p, n) for p, n in res["prioritats"] if nivell_prioritat(p) == "alta"]
        if altes:
            noms = " o ".join(p for p, _ in altes).lower()
            pct = sum(n for _, n in altes) / n_val * 100
            conc.append(("El ", f"{pct:.1f}%", f" de les incidències són de prioritat {noms}.", True))
    if te_data:
        (a, m), n = Counter((r["_data"].year, r["_data"].month) for r in valides).most_common(1)[0]
        dia, _ = Counter(r["_data"].weekday() for r in valides).most_common(1)[0]
        conc.append(("El mes amb més incidències va ser ", f"{MESOS[m - 1]} {a}", f" ({n}).", False))
        conc.append(("El dia de la setmana amb més incidències és el ", DIES[dia].lower(), ".", False))
    if amb_descarts:
        conc.append(("S'han descartat ", str(total - n_val), " registres erronis o duplicats.", False))
    return res


# ---------------------------------------------------------------------------
# 5a. PRESENTACIÓ: terminal (colors ANSI)
# ---------------------------------------------------------------------------
def es_terminal(flux):
    try:
        return flux is not None and flux.isatty()
    except (AttributeError, ValueError, OSError):
        return False


def activar_colors_windows():
    """A Windows cal activar les seqüències ANSI a la consola; si no es pot, sense colors."""
    if os.name != "nt":
        return True
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.GetStdHandle(-11)            # STD_OUTPUT_HANDLE
        mode = ctypes.c_uint32()
        if not kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            return False
        return bool(kernel32.SetConsoleMode(handle, mode.value | 0x0004))  # VIRTUAL_TERMINAL_PROCESSING
    except Exception:
        return False


def configurar_sortida():
    """Evita errors de codificació amb ═ █ ▸ i accents (p. ex. en redirigir a fitxer a Windows)."""
    for flux in (sys.stdout, sys.stderr):
        try:
            if es_terminal(flux):
                flux.reconfigure(errors="replace")
            else:
                flux.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError, OSError):
            pass


# Colors només si la sortida és un terminal de veritat: res de codis estranys en redirigir
# a un fitxer (> sortida.txt) o a un altre programa. Es respecta la convenció NO_COLOR.
USA_COLOR = (es_terminal(sys.stdout) and "--no-color" not in sys.argv
             and "NO_COLOR" not in os.environ and os.environ.get("TERM") != "dumb"
             and activar_colors_windows())
NEGRETA, VERMELL, VERD, GROC, BLAU, MAGENTA, CIAN, GRIS = "1", "31", "32", "33", "34", "35", "36", "90"
COLOR_NIVELL = {"alta": VERMELL, "mitja": GROC, "baixa": VERD}
AMPLE_BARRA = 30


def col(text, *codis):
    if not USA_COLOR:
        return str(text)
    return f"\033[{';'.join(codis)}m{text}\033[0m"


def error(missatge):
    """Missatge d'error a stderr (es veu encara que la sortida normal vagi a un fitxer)."""
    if es_terminal(sys.stderr) and "--no-color" not in sys.argv and "NO_COLOR" not in os.environ:
        missatge = f"\033[1;31m{missatge}\033[0m"
    print(f"  {missatge}", file=sys.stderr)


def retallar(text, maxim):
    """Talla els textos massa llargs per no desquadrar les columnes del terminal."""
    text = str(text)
    return text if len(text) <= maxim else text[:maxim - 1] + "…"


def titol(text):
    print()
    print(col(f" {retallar(text, 66)} ".center(72, "═"), NEGRETA, CIAN))


def percentatge(n, total):
    p = n / total * 100
    return " <0.1%" if 0 < p < 0.1 else f"{p:5.1f}%"


def taula(files, total, color_fn=None):
    """files = llista de (etiqueta, quantitat). Mostra quantitat, percentatge i barra."""
    if not files:
        print(col("  (sense dades)", GRIS))
        return
    maxim = max(n for _, n in files) or 1
    for etiqueta, n in files:
        barra = "█" * max(1, round(n / maxim * AMPLE_BARRA)) if n else ""
        color = color_fn(etiqueta) if color_fn else VERD
        nom = retallar(etiqueta, 28).ljust(28)
        print(f"  {nom} {n:>6} {percentatge(n, total)}  {col(barra, color)}")


def color_prioritat(valor):
    return COLOR_NIVELL[nivell_prioritat(valor)]


def mostrar_terminal(res):
    print(col("\n  ANÀLISI D'INCIDÈNCIES INFORMÀTIQUES I AUDIOVISUALS", NEGRETA, MAGENTA))
    print(col(f"  Fitxer: {res['fitxer']}   ·   Data de l'informe: {res['data_informe']:%d/%m/%Y}", GRIS))

    titol("CAMPS DETECTATS")
    for rol, etiqueta in res["camps"]:
        print(f"  {rol:<14} → {col(retallar(etiqueta, 55), VERD) if etiqueta else col('no trobat', GRIS)}")

    q = res["qualitat"]
    total, n_val = q["total"], q["valides"]
    if not n_val:
        return

    titol("QUALITAT DE LES DADES")
    print(f"  Registres llegits:     {col(total, NEGRETA)}")
    print(f"  Incidències vàlides:   {col(n_val, NEGRETA, VERD)}  ({n_val / total * 100:.1f}%)")
    print(f"  Descartades:           {col(q['descartades'], NEGRETA, VERMELL)}  ({q['descartades'] / total * 100:.1f}%)")
    for motiu, n in q["motius"]:
        print(col(f"      · {motiu:<38} {n:>5}", GRIS))

    seccions = [
        ("dispositius", "INCIDÈNCIES PER DISPOSITIU", lambda _: BLAU),
        ("prioritats", "INCIDÈNCIES PER PRIORITAT", color_prioritat),
        ("llocs", "TOP 10 LLOCS AMB MÉS INCIDÈNCIES", lambda _: MAGENTA),
        ("usuaris", "USUARIS AFECTATS PER INCIDÈNCIA", lambda _: GROC),
        ("mensual", "EVOLUCIÓ MENSUAL", lambda _: CIAN),
        ("dies_setmana", "PER DIA DE LA SETMANA", lambda _: CIAN),
    ]
    for clau, nom, color_fn in seccions:
        if res[clau] is not None:
            titol(nom)
            taula(res[clau], n_val, color_fn)

    if res["creuada"]:
        titol("DISPOSITIU × PRIORITAT")
        cols = res["creuada"]["columnes"]
        print(col("  " + " " * 24 + "".join(c[:9].rjust(10) for c in cols) + "     Total", NEGRETA))
        for f, valors in res["creuada"]["valors"].items():
            linia = "".join(col(str(v).rjust(10), color_prioritat(c)) for v, c in zip(valors, cols))
            print(f"  {retallar(f, 23).ljust(24)}{linia}{sum(valors):>10}")

    if res["informadors"] is not None:
        titol("PERSONES QUE INFORMEN MÉS INCIDÈNCIES (TOP 5)")
        taula(res["informadors"], n_val, lambda _: GRIS)

    for etiqueta, files in res["altres"]:
        titol(f"DISTRIBUCIÓ: {etiqueta.upper()}")
        taula(files, n_val)

    titol("CONCLUSIONS")
    for abans, destacat, despres, alerta in res["conclusions"]:
        codis = (NEGRETA, VERMELL) if alerta else (NEGRETA,)
        print(f"  ▸ {abans}{col(retallar(destacat, 60), *codis)}{despres}")
    print()


# ---------------------------------------------------------------------------
# 5b. PRESENTACIÓ: informe HTML (autocontingut, sense dependències externes)
# ---------------------------------------------------------------------------
CSS = """
:root {
  --fons: #f6f7f9; --targeta: #ffffff; --text: #1d2330; --suau: #667085; --linia: #e4e7ec;
  --pista: #eef0f3; --accent: #3b5bdb;
  --blau: #3b82f6; --magenta: #c026d3; --cian: #0891b2; --groc: #d97706; --gris: #8a94a6;
  --alta: #dc2626; --mitja: #d97706; --baixa: #16a34a;
}
@media (prefers-color-scheme: dark) {
  :root {
    --fons: #111418; --targeta: #1a1f26; --text: #e6e9ee; --suau: #9aa4b2; --linia: #2a313b;
    --pista: #252c35; --accent: #7c95ff;
    --blau: #60a5fa; --magenta: #e879f9; --cian: #22d3ee; --groc: #fbbf24; --gris: #9aa4b2;
    --alta: #f87171; --mitja: #fbbf24; --baixa: #4ade80;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--fons); color: var(--text);
       font: 15px/1.5 system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
/* Textos molt llargs sense espais: es parteixen en lloc de desbordar la pàgina */
header, h2, p, li { overflow-wrap: anywhere; }
main { max-width: 980px; margin: 0 auto; padding: 32px 16px 48px; }
header h1 { margin: 0 0 4px; font-size: 1.6rem; letter-spacing: -0.01em; }
header p { margin: 0; color: var(--suau); }
.kpis { display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr)); gap: 12px; margin: 24px 0; }
.kpi { background: var(--targeta); border: 1px solid var(--linia); border-radius: 10px; padding: 14px 16px; }
.kpi .v { font-size: 1.7rem; font-weight: 650; font-variant-numeric: tabular-nums; }
.kpi .e { color: var(--suau); font-size: .85rem; }
.kpi.ok .v { color: var(--baixa); } .kpi.ko .v { color: var(--alta); }
.graella { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(420px, 100%), 1fr)); gap: 16px; }
section { background: var(--targeta); border: 1px solid var(--linia); border-radius: 10px;
          padding: 16px 18px; margin-bottom: 16px; min-width: 0; }
.graella section { margin-bottom: 0; }
.graella + section, section + .graella { margin-top: 16px; }
h2 { font-size: 1rem; margin: 0 0 12px; }
.taula-scroll { overflow-x: auto; }
table { width: 100%; border-collapse: collapse; font-variant-numeric: tabular-nums; }
th, td { padding: 5px 6px; text-align: left; border-bottom: 1px solid var(--linia); white-space: nowrap; }
th { color: var(--suau); font-weight: 600; font-size: .85rem; }
td.n, th.n { text-align: right; }
td.pct { color: var(--suau); text-align: right; width: 4.5em; }
td.barra { width: 40%; min-width: 80px; }
.pista { background: var(--pista); border-radius: 4px; height: 10px; }
.omplert { height: 10px; border-radius: 4px; min-width: 2px; }
.c-blau { background: var(--blau); } .c-magenta { background: var(--magenta); }
.c-cian { background: var(--cian); } .c-groc { background: var(--groc); }
.c-gris { background: var(--gris); } .c-verd, .c-baixa { background: var(--baixa); }
.c-alta { background: var(--alta); } .c-mitja { background: var(--mitja); }
.t-alta { color: var(--alta); } .t-mitja { color: var(--mitja); } .t-baixa { color: var(--baixa); }
td.etq { max-width: 260px; overflow: hidden; text-overflow: ellipsis; }
ul.motius { margin: 8px 0 0; padding-left: 18px; color: var(--suau); }
ul.conclusions { margin: 0; padding-left: 18px; }
ul.conclusions li { margin: 4px 0; }
.alerta { color: var(--alta); }
.no-trobat { color: var(--suau); font-style: italic; }
footer { color: var(--suau); font-size: .8rem; text-align: center; margin-top: 24px; }
/* Gràfic de pastís (SVG) de la prioritat */
.pastis-bloc { display: flex; flex-wrap: wrap; gap: 20px; align-items: center; }
.pastis-bloc svg { width: 150px; height: 150px; flex: none; }
.pastis-bloc .taula-scroll { flex: 1 1 220px; min-width: 0; }
.s-alta { stroke: var(--alta); } .s-mitja { stroke: var(--mitja); } .s-baixa { stroke: var(--baixa); }
/* Taula creuada: cada cel·la amb el color de la seva prioritat */
td.t-alta, td.t-mitja, td.t-baixa { font-weight: 600; }
@media (max-width: 520px) {
  /* Al mòbil les etiquetes llargues passen a dues línies en lloc de desbordar */
  td.etq { white-space: normal; max-width: none; overflow-wrap: anywhere; }
  td.etq > span { display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2;
                  line-clamp: 2; overflow: hidden; }
  td.barra { width: 25%; min-width: 50px; }
  th, td { padding: 5px 4px; }
}
/* Impressió i "Desa com a PDF": sempre colors clars, sense tallar seccions */
@page { margin: 14mm; }
@media print {
  :root {
    --fons: #ffffff; --targeta: #ffffff; --text: #000000; --suau: #555555; --linia: #cccccc;
    --pista: #eeeeee; --blau: #3b82f6; --magenta: #c026d3; --cian: #0891b2; --groc: #d97706;
    --gris: #8a94a6; --alta: #dc2626; --mitja: #d97706; --baixa: #16a34a;
  }
  * { -webkit-print-color-adjust: exact; print-color-adjust: exact; }
  body { font-size: 12px; }
  main { max-width: none; padding: 0 2px; }
  .kpis { grid-template-columns: repeat(4, 1fr); }
  section, .kpi { break-inside: avoid; page-break-inside: avoid; box-shadow: none; }
  .graella { grid-template-columns: 1fr 1fr; }
  .taula-scroll { overflow: visible; }
  td.etq { max-width: 180px; }
}
"""


def h(text):
    return html.escape(str(text))


def html_taula(files, total, classe_fn):
    if not files:
        return '<p class="no-trobat">(sense dades)</p>'
    maxim = max(n for _, n in files) or 1
    linies = []
    for etiqueta, n in files:
        ample = n / maxim * 100
        linies.append(
            f'<tr><td class="etq" title="{h(etiqueta)}"><span>{h(etiqueta)}</span></td>'
            f'<td class="n">{n}</td><td class="pct">{h(percentatge(n, total).strip())}</td>'
            f'<td class="barra"><div class="pista"><div class="omplert c-{classe_fn(etiqueta)}" '
            f'style="width:{ample:.1f}%"></div></div></td></tr>')
    return ('<div class="taula-scroll"><table><thead><tr><th></th><th class="n">Incidències</th>'
            '<th class="n">%</th><th></th></tr></thead><tbody>' + "".join(linies) +
            "</tbody></table></div>")


def html_seccio(titol_seccio, contingut):
    return f"<section><h2>{h(titol_seccio)}</h2>{contingut}</section>"


def html_pastis(files):
    """Gràfic de pastís en SVG pur: cada porció és un cercle amb un traç discontinu.

    Amb radi r i gruix de traç 2r, el traç omple tot el cercle; stroke-dasharray
    marca quina part de la circumferència ocupa cada porció.
    """
    total = sum(n for _, n in files) or 1
    r = 16
    circumferencia = 2 * math.pi * r
    porcions, acumulat = [], 0.0
    for etiqueta, n in files:
        llarg = n / total * circumferencia
        porcions.append(
            f'<circle r="{r}" cx="32" cy="32" fill="none" class="s-{nivell_prioritat(etiqueta)}" '
            f'stroke-width="{2 * r}" stroke-dasharray="{llarg:.3f} {circumferencia:.3f}" '
            f'stroke-dashoffset="{-acumulat:.3f}" transform="rotate(-90 32 32)">'
            f'<title>{h(etiqueta)}: {n} ({n / total * 100:.1f}%)</title></circle>')
        acumulat += llarg
    return ('<svg viewBox="0 0 64 64" role="img" aria-label="Gràfic de pastís de les prioritats">'
            + "".join(porcions) + "</svg>")


def escriure_html(res, fitxer_html=FITXER_HTML):
    q = res["qualitat"]
    total, n_val = q["total"], q["valides"]
    parts = []

    # Capçalera
    parts.append(f"""<header><h1>Anàlisi d'incidències informàtiques i audiovisuals</h1>
<p>Fitxer analitzat: <strong>{h(res['fitxer'])}</strong> · Data de l'informe: {res['data_informe']:%d/%m/%Y}</p></header>""")

    # Targetes amb els números clau
    if res["prioritats"] and n_val:
        n_alta = sum(n for p, n in res["prioritats"] if nivell_prioritat(p) == "alta")
        pct_alta = f"{n_alta / n_val * 100:.1f}%"
    else:
        pct_alta = "—"
    kpis = [("", total, "Registres llegits"),
            ("ok", n_val, f"Incidències vàlides ({n_val / total * 100:.1f}%)" if total else "Incidències vàlides"),
            ("ko", q["descartades"], "Registres descartats"),
            ("ko", pct_alta, "Prioritat alta / crítica")]
    parts.append('<div class="kpis">' + "".join(
        f'<div class="kpi {c}"><div class="v">{h(v)}</div><div class="e">{h(e)}</div></div>'
        for c, v, e in kpis) + "</div>")

    if n_val:
        # Qualitat de les dades
        motius = "".join(f"<li>{h(m)}: <strong>{n}</strong></li>" for m, n in q["motius"])
        parts.append(html_seccio("Qualitat de les dades",
                                 f"<p>S'han descartat {q['descartades']} de {total} registres "
                                 f"({q['descartades'] / total * 100:.1f}%).</p>"
                                 + (f'<ul class="motius">{motius}</ul>' if motius
                                    else "<p>No s'ha descartat cap registre.</p>")))

        # Prioritat: pastís + barres (les barres fan de llegenda amb els mateixos colors)
        if res["prioritats"] is not None:
            parts.append(html_seccio("Incidències per prioritat",
                                     '<div class="pastis-bloc">' + html_pastis(res["prioritats"])
                                     + html_taula(res["prioritats"], n_val, nivell_prioritat) + "</div>"))

        # Resta de distribucions, en una graella (dues columnes si hi caben)
        seccions = [
            ("dispositius", "Incidències per dispositiu", lambda _: "blau"),
            ("llocs", "Top 10 llocs amb més incidències", lambda _: "magenta"),
            ("usuaris", "Usuaris afectats per incidència", lambda _: "groc"),
            ("mensual", "Evolució mensual", lambda _: "cian"),
            ("dies_setmana", "Per dia de la setmana", lambda _: "cian"),
            ("informadors", "Persones que informen més incidències (top 5)", lambda _: "gris"),
        ]
        blocs = [html_seccio(t, html_taula(res[k], n_val, fn)) for k, t, fn in seccions if res[k] is not None]
        blocs += [html_seccio(f"Distribució: {et}", html_taula(files, n_val, lambda _: "verd"))
                  for et, files in res["altres"]]
        parts.append('<div class="graella">' + "".join(blocs) + "</div>")

        # Taula creuada: cada columna (i les seves cel·les) amb el color de la prioritat
        if res["creuada"]:
            cols = res["creuada"]["columnes"]
            nivells = [nivell_prioritat(c) for c in cols]
            cap = "".join(f'<th class="n t-{nv}" title="{h(c)}">{h(c[:12])}</th>' for c, nv in zip(cols, nivells))
            files = "".join(
                f'<tr><td class="etq" title="{h(f)}"><span>{h(f)}</span></td>'
                + "".join(f'<td class="n t-{nv}">{v}</td>' for v, nv in zip(valors, nivells))
                + f'<td class="n"><strong>{sum(valors)}</strong></td></tr>'
                for f, valors in res["creuada"]["valors"].items())
            totals = [sum(v[i] for v in res["creuada"]["valors"].values()) for i in range(len(cols))]
            peu = ('<tr><th>Total</th>' + "".join(f'<th class="n">{t}</th>' for t in totals)
                   + f'<th class="n">{sum(totals)}</th></tr>')
            parts.append(html_seccio("Dispositiu × prioritat",
                                     f'<div class="taula-scroll"><table><thead><tr><th>Dispositiu</th>{cap}'
                                     f'<th class="n">Total</th></tr></thead><tbody>{files}</tbody>'
                                     f'<tfoot>{peu}</tfoot></table></div>'))
    else:
        parts.append(html_seccio("Sense dades",
                                 "<p>Cap incidència vàlida. Revisa els camps detectats (variable CAMPS).</p>"))

    # Camps detectats (annex)
    camps = "".join(f"<tr><td>{h(rol)}</td><td>{h(et) if et else '<span class=no-trobat>no trobat</span>'}</td></tr>"
                    for rol, et in res["camps"])
    parts.append(html_seccio("Camps detectats a l'XML",
                             f'<div class="taula-scroll"><table><thead><tr><th>Rol</th><th>Etiqueta XML</th>'
                             f'</tr></thead><tbody>{camps}</tbody></table></div>'))

    # Conclusions, al final de l'informe
    if res["conclusions"]:
        items = "".join(
            f'<li>{h(a)}<strong class="{"alerta" if al else ""}">{h(d)}</strong>{h(p)}</li>'
            for a, d, p, al in res["conclusions"])
        parts.append(html_seccio("Conclusions", f'<ul class="conclusions">{items}</ul>'))

    document = f"""<!DOCTYPE html>
<html lang="ca">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Informe d'incidències</title>
<style>{CSS}</style>
</head>
<body>
<main>
{"".join(parts)}
<footer>Generat per ProcessarIncidencies.py el {datetime.now():%d/%m/%Y a les %H:%M}</footer>
</main>
</body>
</html>
"""
    ruta = Path(fitxer_html).resolve()
    try:
        escriure_fitxer_segur(ruta, document)
    except OSError as e:
        error(f"No s'ha pogut desar l'informe HTML. {descriure_error(e, ruta)}.")
        return None
    return ruta


# ---------------------------------------------------------------------------
# 6. Desar a JSON
# ---------------------------------------------------------------------------
def marca_temporal_iso(text):
    """'2026/10/27 10:35:45 p. m. CET' -> '2026-10-27T22:35:45'. Si no hi ha hora, només la data."""
    m = re.match(r"(\d{4})[/-](\d{1,2})[/-](\d{1,2})[ T]+(\d{1,2}):(\d{2})(?::(\d{2}))?\s*([ap])?", norm(text))
    if m:
        a, mes, d, hh, mm, ss, ampm = m.groups()
        hh = int(hh)
        if ampm == "p" and hh < 12:
            hh += 12
        elif ampm == "a" and hh == 12:
            hh = 0
        try:
            return datetime(int(a), int(mes), int(d), hh, int(mm), int(ss or 0)).isoformat()
        except ValueError:
            pass
    d = llegir_data(text)
    return d.isoformat() if d else text


def incidencia_json(r, rols):
    """Converteix un registre vàlid en un dict serialitzable: amb ID, dates ISO i sense camps interns."""
    inc = {"id": r["_id"]}
    for k, v in r.items():
        if k.startswith("_") or k == "id":
            continue
        if k == rols.get("data"):
            v = r["_data"].isoformat() if "_data" in r else v
        elif k == rols.get("timestamp") and v:
            v = marca_temporal_iso(v)
        inc[k] = v
    return inc


def a_diccionari(files):
    return None if files is None else {str(k): n for k, n in files}


def estadistiques_json(incidencies, font):
    """Recalcula les estadístiques sobre la llista final d'incidències del JSON."""
    if not incidencies:
        return {}
    copies = [dict(i) for i in incidencies]           # no modifiquem les originals
    etiquetes = []
    for i in copies:
        etiquetes += [k for k in i if k != "id" and k not in etiquetes]
    rols = detectar_camps(etiquetes)
    preparar(copies, rols)
    camp_data = rols.get("data") or rols.get("timestamp")
    for i in copies:
        d = llegir_data(i.get(camp_data)) if camp_data else None
        if d:
            i["_data"] = d
    res = calcular_estadistiques(font, copies, etiquetes, rols, copies, Counter(), amb_descarts=False)

    creuada = None
    if res["creuada"]:
        cols = res["creuada"]["columnes"]
        creuada = {f: dict(zip(cols, v)) for f, v in res["creuada"]["valors"].items()}
    return {
        "per_dispositiu": a_diccionari(res["dispositius"]),
        "per_prioritat": a_diccionari(res["prioritats"]),
        "top_10_llocs": a_diccionari(res["llocs"]),
        "usuaris_afectats": a_diccionari(res["usuaris"]),
        "evolucio_mensual": a_diccionari(res["mensual"]),
        "per_dia_setmana": a_diccionari(res["dies_setmana"]),
        "dispositiu_x_prioritat": creuada,
        "top_5_informadors": a_diccionari(res["informadors"]),
        "altres_camps": {et: a_diccionari(files) for et, files in res["altres"]},
        "conclusions": [f"{a}{d}{p}" for a, d, p, _ in res["conclusions"]],
    }


class JsonIllegible(Exception):
    """El fitxer existeix però no es pot llegir (permisos...): NO es pot tractar com a corrupte,
    perquè llavors s'oferiria sobreescriure dades que potser són bones."""


def llegir_json_existent(ruta):
    """Retorna (dades, None) si el JSON és correcte o (None, motiu) si està corrupte.
    Llança JsonIllegible si ni tan sols es pot obrir."""
    try:
        with open(ruta, "rb") as f:
            cru = f.read()
    except OSError as e:
        raise JsonIllegible(descriure_error(e, ruta)) from None
    try:
        dades = json.loads(cru.decode("utf-8"))
    except UnicodeDecodeError:
        return None, "no està en UTF-8"
    except json.JSONDecodeError as e:
        return None, f"no és un JSON vàlid (línia {e.lineno}, columna {e.colno})"
    except RecursionError:
        return None, "té massa nivells d'anidament"
    if not isinstance(dades, dict) or not isinstance(dades.get("incidencies"), list):
        return None, "no té la clau \"incidencies\" amb una llista"
    for i in dades["incidencies"]:
        if not isinstance(i, dict) or not isinstance(i.get("id"), (str, int)) or isinstance(i.get("id"), bool):
            return None, "hi ha incidències sense un \"id\" vàlid"
        if not all(isinstance(v, str) for k, v in i.items() if k != "id"):
            return None, "hi ha incidències amb valors que no són text"
    return dades, None


def preguntar(missatge, opcions):
    """Pregunta fins que la resposta sigui una de les lletres d'opcions.

    - La pregunta s'escriu a stderr: es veu encara que la sortida vagi a un fitxer (> sortida.txt).
    - Ctrl+C o Ctrl+D (o una entrada que s'acaba) equivalen a cancel·lar.
    - Si l'entrada no és un terminal (un script, cron...), no es pregunta: es cancel·la, per no
      quedar bloquejat esperant una resposta que no arribarà mai.
    """
    if not es_terminal(sys.stdin):
        error("No es pot preguntar perquè l'entrada no és un terminal. "
              "Fes servir --json-mode=sobreescriure o --json-mode=afegir.")
        return "C"
    while True:
        try:
            sys.stderr.write(missatge)
            sys.stderr.flush()
            resposta = input().strip().upper()
        except (EOFError, KeyboardInterrupt):
            sys.stderr.write("\n")
            return "C"
        if resposta in opcions:
            return resposta
        sys.stderr.write(f"  Opció no vàlida. Escriu {', '.join(opcions[:-1])} o {opcions[-1]}.\n")


def escriure_fitxer_segur(ruta, contingut):
    """Escriu a un temporal de la mateixa carpeta i el reanomena (os.replace és atòmic):
    si el programa s'interromp, el fitxer anterior queda intacte."""
    ruta = os.path.abspath(ruta)
    if os.path.isdir(ruta):
        raise IsADirectoryError(errno.EISDIR, "és una carpeta", ruta)
    if os.path.exists(ruta) and not os.access(ruta, os.W_OK):
        raise PermissionError(errno.EACCES, "fitxer de només lectura", ruta)
    fd, temporal = tempfile.mkstemp(prefix=".incidencies-", suffix=".tmp", dir=os.path.dirname(ruta))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(contingut)
            f.flush()
            os.fsync(f.fileno())
        # mkstemp el crea amb permisos 0600: posem els del fitxer anterior o els habituals
        if os.path.exists(ruta):
            permisos = stat.S_IMODE(os.stat(ruta).st_mode)
        else:
            umask = os.umask(0)
            os.umask(umask)
            permisos = 0o666 & ~umask
        os.chmod(temporal, permisos)
        os.replace(temporal, ruta)
    except BaseException:
        if os.path.exists(temporal):
            os.remove(temporal)
        raise


def escriure_json_segur(ruta, dades):
    escriure_fitxer_segur(ruta, json.dumps(dades, ensure_ascii=False, indent=2) + "\n")


def desar_json(valides, rols, font, ruta, mode=None):
    """Desa les incidències vàlides a `ruta`. mode: None (preguntar), 'sobreescriure' o 'afegir'.
    Retorna False només si hi ha hagut un error (cancel·lar no és un error)."""
    noves = [incidencia_json(r, rols) for r in valides]
    existents, fonts = [], [font]
    existia = os.path.exists(ruta)

    if existia:
        try:
            dades, problema = llegir_json_existent(ruta)
        except JsonIllegible as e:
            error(f"No es pot llegir el JSON existent ({e}). No s'ha tocat.")
            return False
        if problema:
            error(f"Atenció: {ruta} {problema}.")
            if mode == "afegir":
                error("No s'hi pot afegir res. No s'ha tocat el fitxer "
                      "(fes servir --json-mode=sobreescriure per substituir-lo).")
                return False
            if mode is None:
                mode = {"S": "sobreescriure", "C": None}[
                    preguntar(f"  {ruta} està malmès. [S] Sobreescriure'l  [C] Cancel·lar: ", ["S", "C"])]
        elif mode is None:
            mode = {"S": "sobreescriure", "A": "afegir", "C": None}[
                preguntar(f"  {ruta} ja existeix ({len(dades['incidencies'])} incidències). "
                          "[S] Sobreescriure  [A] Afegir  [C] Cancel·lar: ", ["S", "A", "C"])]
        if mode is None:
            print(col(f"  Cancel·lat: {ruta} no s'ha modificat.", GRIS))
            return True
        if mode == "afegir":
            existents = dades["incidencies"]
            fonts = [f for f in str(dades.get("font", "")).split(", ") if f]
            if font not in fonts:
                fonts.append(font)

    ids = {str(i["id"]) for i in existents}
    afegides = [i for i in noves if str(i["id"]) not in ids]
    totes = existents + afegides

    dades = {
        "generat": datetime.now().isoformat(timespec="seconds"),
        "font": ", ".join(fonts),
        "total_incidencies": len(totes),
        "estadistiques": estadistiques_json(totes, ", ".join(fonts)),
        "incidencies": totes,
    }
    try:
        escriure_json_segur(ruta, dades)
    except OSError as e:
        error(f"No s'ha pogut desar el JSON. {descriure_error(e, os.path.abspath(ruta))}.")
        return False

    ruta_abs = os.path.abspath(ruta)
    if not existia:
        print(col(f"  JSON creat a: {ruta_abs} ({len(totes)} incidències)", NEGRETA, VERD))
    elif mode == "afegir":
        print(col(f"  JSON actualitzat: {ruta_abs}", NEGRETA, VERD))
        print(f"      · Hi havia:                 {len(existents):>6}")
        print(f"      · Afegides:                 {len(afegides):>6}")
        print(f"      · Ignorades (ID repetit):   {len(noves) - len(afegides):>6}")
        print(f"      · Total ara:                {len(totes):>6}")
    else:
        print(col(f"  JSON sobreescrit: {ruta_abs} ({len(totes)} incidències)", NEGRETA, VERD))
    return True


# ---------------------------------------------------------------------------
# Programa principal
# ---------------------------------------------------------------------------
OPCIONS_SIMPLES = {"--no-color", "--no-obrir", "--debug"}
OPCIONS_AMB_VALOR = {"--html", "--json", "--json-mode"}


def opcio(nom, defecte=None):
    """Valor d'una opció --nom=valor de la línia d'ordres."""
    return next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith(f"--{nom}=")), defecte)


def comprovar_arguments():
    """Atura el programa amb un missatge clar si hi ha opcions desconegudes o mal escrites."""
    fitxers = []
    for a in sys.argv[1:]:
        if not a.startswith("--"):
            fitxers.append(a)
        elif a.split("=", 1)[0] in OPCIONS_AMB_VALOR:
            if "=" not in a or not a.split("=", 1)[1].strip():
                sys.exit(f"L'opció {a.split('=', 1)[0]} necessita un valor (p. ex. {a.split('=', 1)[0]}=valor).")
        elif a not in OPCIONS_SIMPLES:
            valides = ", ".join(sorted(OPCIONS_SIMPLES) + [o + "=..." for o in sorted(OPCIONS_AMB_VALOR)])
            sys.exit(f"Opció desconeguda: {a}\nOpcions vàlides: {valides}")
    if len(fitxers) > 1:
        sys.exit(f"Només es pot indicar un fitxer XML (n'has posat {len(fitxers)}: {', '.join(fitxers)}).")


def hi_ha_entorn_grafic():
    """A Linux/BSD sense DISPLAY ni WAYLAND_DISPLAY (servidor, SSH...) webbrowser podria engegar un
    navegador de text (lynx, w3m...) que ocuparia el terminal: en aquest cas no s'obre res."""
    if os.environ.get("BROWSER"):                 # l'usuari ha triat navegador explícitament
        return True
    if sys.platform.startswith(("linux", "freebsd", "openbsd", "netbsd")):
        return bool(os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY"))
    return True                                   # Windows i macOS sempre en tenen


def obrir_navegador(ruta):
    if not hi_ha_entorn_grafic():
        print(col("  No hi ha entorn gràfic: no s'obre el navegador. Obre el fitxer manualment.", GRIS))
        return
    try:
        obert = webbrowser.open(ruta.as_uri())
    except Exception:                             # webbrowser.Error, OSError...
        obert = False
    if obert:
        print(col("  S'ha obert al navegador.", GRIS))
    else:
        print(col("  No s'ha pogut obrir el navegador; obre el fitxer manualment.", GRIS))


def main():
    configurar_sortida()
    comprovar_arguments()
    fitxer = next((a for a in sys.argv[1:] if not a.startswith("--")), FITXER)
    fitxer_html = opcio("html", FITXER_HTML)
    fitxer_json = opcio("json", FITXER_JSON)
    mode_json = opcio("json-mode")
    if mode_json is not None:
        mode_json = mode_json.lower()
        if mode_json not in MODES_JSON:
            sys.exit(f"--json-mode ha de ser {' o '.join(MODES_JSON)} (has posat '{mode_json}').")

    registres, etiquetes = llegir_xml(fitxer)
    if not registres:
        sys.exit(f"L'XML {fitxer} no conté cap incidència. No s'ha generat cap informe.")
    rols = detectar_camps(etiquetes)
    preparar(registres, rols)
    valides, motius = filtrar(registres, rols)

    res = calcular_estadistiques(fitxer, registres, etiquetes, rols, valides, motius)
    mostrar_terminal(res)
    sortida = escriure_html(res, fitxer_html)

    if not res["qualitat"]["valides"]:
        sys.exit("\nCap incidència vàlida després del filtratge. Revisa els camps detectats (variable CAMPS).\n"
                 + (f"Informe HTML desat a: {sortida}\n" if sortida else "")
                 + "No s'ha modificat el JSON.")
    if sortida:
        print(col(f"  Informe HTML desat a: {sortida}", NEGRETA, VERD))

    json_correcte = desar_json(valides, rols, fitxer, fitxer_json, mode_json)

    if sortida and "--no-obrir" not in sys.argv:
        obrir_navegador(sortida)
    print()
    if not (sortida and json_correcte):
        sys.exit(1)


def executar():
    """Punt d'entrada: cap error acaba en un traceback de Python (excepte amb --debug)."""
    try:
        main()
    except KeyboardInterrupt:
        print("\n  Interromput per l'usuari (Ctrl+C). No s'ha deixat cap fitxer a mitges.", file=sys.stderr)
        sys.exit(130)
    except BrokenPipeError:
        # La sortida anava a un programa que ja ha acabat (p. ex. | head): sortim en silenci
        try:
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except (OSError, AttributeError, ValueError):
            pass
        sys.exit(1)
    except MemoryError:
        sys.exit("No hi ha prou memòria per processar aquest fitxer.")
    except Exception as e:
        if "--debug" in sys.argv:
            raise
        sys.exit(f"Error inesperat: {type(e).__name__}: {e}\n"
                 "Torna-ho a executar amb --debug per veure'n els detalls.")


if __name__ == "__main__":
    executar()
