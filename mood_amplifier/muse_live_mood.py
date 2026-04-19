"""
Muse Live Mood Readout
Listens for OSC packets from Mind Monitor on UDP port 5000
and displays a real-time mood readout in the terminal.

Run on the Acer (the machine on the same WiFi as the phone):
    python -m pip install python-osc
    python muse_live_mood.py

Mind Monitor settings on the phone:
    OSC Stream Target IP : <your Acer's LAN IP, e.g. 192.168.x.46>
    OSC Stream Port      : 5000
    OSC Stream toggle    : ON
"""
import os
import time
import collections
from pythonosc import dispatcher, osc_server

CHANS = ["TP9", "AF7", "AF8", "TP10"]
WIN = collections.defaultdict(lambda: collections.deque(maxlen=50))  # ~5s @ 10Hz
contact = [9, 9, 9, 9]
last_render = [0.0]
packet_count = [0]


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


def make_band_handler(band):
    def handler(addr, *args):
        store(band, args)
    return handler


def avg(d):
    return sum(d) / len(d) if d else 0.0


def render(addr=None, *args):
    packet_count[0] += 1
    now = time.time()
    if now - last_render[0] < 1.0:
        return
    last_render[0] = now

    os.system("cls" if os.name == "nt" else "clear")
    print("=" * 60)
    print(" MUSE LIVE MOOD READOUT          (Ctrl+C to stop)")
    print("=" * 60)

    sym = {1: "GOOD", 2: " OK ", 3: "POOR", 4: "POOR"}
    contact_str = "  ".join(
        f"{CHANS[i]}={sym.get(contact[i], 'POOR')}" for i in range(4)
    )
    print(f" Contact:  {contact_str}")
    print(f" Packets received: {packet_count[0]}")
    print()

    for b in ("theta", "alpha", "beta"):
        m = sum(avg(WIN[(b, i)]) for i in range(4)) / 4
        bar_len = max(0, min(40, int((m + 1) * 20)))
        bar = "#" * bar_len
        print(f" {b.upper():5s}  {m:+.2f}  |{bar:<40s}|")

    a = sum(avg(WIN[("alpha", i)]) for i in range(4)) / 4
    bb = sum(avg(WIN[("beta", i)]) for i in range(4)) / 4
    t = sum(avg(WIN[("theta", i)]) for i in range(4)) / 4

    ab = a / bb if bb else 0
    tb = t / bb if bb else 0

    print()
    print(f" Alpha/Beta (relaxation index): {ab:.2f}")
    print(f" Theta/Beta (meditation index): {tb:.2f}")

    state = "ALERT"
    if ab > 1.5:
        state = "RELAXED"
    if tb > 1.5:
        state = "MEDITATIVE"
    if ab < 0.6 and tb < 0.6:
        state = "FOCUSED"

    print(f" STATE:    {state}")
    print("=" * 60)


def main():
    d = dispatcher.Dispatcher()
    d.map("/muse/elements/horseshoe", on_horseshoe)
    for b in ("delta", "theta", "alpha", "beta", "gamma"):
        d.map(f"/muse/elements/{b}_absolute", make_band_handler(b))
    d.set_default_handler(render)

    print("Listening on 0.0.0.0:5000 ...")
    print("In Mind Monitor: target IP = your Acer's LAN IP, port = 5000, Stream ON.")
    print("If no packets arrive within 10 seconds: Windows firewall is blocking UDP 5000.")
    print()

    server = osc_server.BlockingOSCUDPServer(("0.0.0.0", 5000), d)
    server.serve_forever()


if __name__ == "__main__":
    main()
