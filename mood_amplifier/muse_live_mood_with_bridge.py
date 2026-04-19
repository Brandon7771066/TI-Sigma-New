"""
Muse Live Mood Readout + Replit Bridge

Listens for Mind Monitor OSC packets on UDP 5000 (LAN),
displays a live terminal readout, AND every 3 seconds posts
the current rolling-average band powers to the Replit
async_gateway.py /api/upload endpoint so the cloud has the
present-moment values too.

Run on the Acer:
    python -m pip install python-osc requests
    python muse_live_mood_with_bridge.py
"""
import os
import time
import threading
import collections
import urllib.parse
import urllib.request
from pythonosc import dispatcher, osc_server

REPLIT_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev:5000"
UPLOAD_PATH = "/api/upload"
POST_INTERVAL_SEC = 3
SESSION_ID = f"ma_{int(time.time())}"

CHANS = ["TP9", "AF7", "AF8", "TP10"]
WIN = collections.defaultdict(lambda: collections.deque(maxlen=50))
contact = [9, 9, 9, 9]
last_render = [0.0]
packet_count = [0]
post_count = [0]
last_post_status = [""]


def store(band, vals):
    for i, v in enumerate(vals[:4]):
        try:
            WIN[(band, i)].append(float(v))
        except (TypeError, ValueError):
            pass


def on_horseshoe(addr, *args):
    global contact
    try:
        contact = [int(float(x)) for x in args[:4]]
    except (TypeError, ValueError):
        pass


def make_handler(b):
    def h(addr, *args):
        store(b, args)
    return h


def avg(d):
    return sum(d) / len(d) if d else 0.0


def chan_avg(band):
    return sum(avg(WIN[(band, i)]) for i in range(4)) / 4


def render(addr=None, *args):
    packet_count[0] += 1
    now = time.time()
    if now - last_render[0] < 1.0:
        return
    last_render[0] = now

    os.system("cls" if os.name == "nt" else "clear")
    print("=" * 64)
    print(" MUSE LIVE MOOD READOUT + REPLIT BRIDGE   (Ctrl+C to stop)")
    print("=" * 64)

    sym = {1: "GOOD", 2: " OK ", 3: "POOR", 4: "POOR"}
    contact_str = "  ".join(
        f"{CHANS[i]}={sym.get(contact[i], 'POOR')}" for i in range(4)
    )
    print(f" Contact:  {contact_str}")
    print(f" Packets received: {packet_count[0]}    Posts to Replit: {post_count[0]}")
    print(f" Last post:        {last_post_status[0]}")
    print(f" Session ID:       {SESSION_ID}")
    print()

    for b in ("theta", "alpha", "beta"):
        m = chan_avg(b)
        bar_len = max(0, min(40, int((m + 1) * 20)))
        bar = "#" * bar_len
        print(f" {b.upper():5s}  {m:+.2f}  |{bar:<40s}|")

    a = chan_avg("alpha")
    bb = chan_avg("beta")
    t = chan_avg("theta")
    ab = a / bb if bb else 0
    tb = t / bb if bb else 0

    print()
    print(f" Alpha/Beta (relaxation): {ab:.2f}")
    print(f" Theta/Beta (meditation): {tb:.2f}")

    state = "ALERT"
    if ab > 1.5:
        state = "RELAXED"
    if tb > 1.5:
        state = "MEDITATIVE"
    if ab < 0.6 and tb < 0.6:
        state = "FOCUSED"

    print(f" STATE:    {state}")
    print("=" * 64)


def post_to_replit():
    while True:
        time.sleep(POST_INTERVAL_SEC)
        try:
            params = {
                "alpha": f"{chan_avg('alpha'):.4f}",
                "beta": f"{chan_avg('beta'):.4f}",
                "theta": f"{chan_avg('theta'):.4f}",
                "gamma": f"{chan_avg('gamma'):.4f}",
                "delta": f"{chan_avg('delta'):.4f}",
                "muse": "1",
                "polar": "0",
                "dev": "Muse2-MindMonitor-Acer",
                "sid": SESSION_ID,
            }
            url = REPLIT_URL + UPLOAD_PATH + "?" + urllib.parse.urlencode(params)
            req = urllib.request.Request(url, method="GET")
            with urllib.request.urlopen(req, timeout=5) as r:
                code = r.status
            post_count[0] += 1
            last_post_status[0] = f"OK {code} at {time.strftime('%H:%M:%S')}"
        except Exception as e:
            last_post_status[0] = f"FAIL: {str(e)[:60]}"


def main():
    d = dispatcher.Dispatcher()
    d.map("/muse/elements/horseshoe", on_horseshoe)
    for b in ("delta", "theta", "alpha", "beta", "gamma"):
        d.map(f"/muse/elements/{b}_absolute", make_handler(b))
    d.set_default_handler(render)

    bridge = threading.Thread(target=post_to_replit, daemon=True)
    bridge.start()

    print(f"Listening on 0.0.0.0:5000 ... Bridge active to {REPLIT_URL}")
    print("Mind Monitor target IP must be your Acer's LAN IP (.46), port 5000.")
    print()

    osc_server.BlockingOSCUDPServer(("0.0.0.0", 5000), d).serve_forever()


if __name__ == "__main__":
    main()
