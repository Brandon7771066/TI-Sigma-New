import sys, json, time, traceback
ds_id = sys.argv[1]
asset_path = sys.argv[2]
from dandi.dandiapi import DandiAPIClient
import h5py, remfile
REPORT_KEYWORDS = ("lick","button","press","response","report","choice","vocaliz","blink","saccade","wheel","trial_outcome","behavior/states","feedback","reward")
out = {"dandiset": ds_id, "asset_path": asset_path}
try:
    with DandiAPIClient() as c:
        a = c.get_dandiset(ds_id, "draft").get_asset_by_path(asset_path)
        s3 = a.get_content_url(follow_redirects=1, strip_query=True)
    rfile = remfile.File(url=s3)
    h5f = h5py.File(rfile, "r")
    stim, rep = [], []
    def walk(name, obj):
        n = name.lower()
        if "stimulus" in n or "stim" in n or "ttl" in n or "trigger" in n or "pulsestim" in n or "/intervals/" in n or "trial" in n:
            stim.append((name, str(getattr(obj,"shape",None))))
        if any(k in n for k in REPORT_KEYWORDS):
            rep.append((name, str(getattr(obj,"shape",None))))
    h5f.visititems(walk)
    out["stim_count"] = len(stim); out["report_count"] = len(rep)
    out["stim_sample"] = stim[:12]; out["report_sample"] = rep[:12]
    if not stim: out["verdict"] = "INELIGIBLE_NO_STIM"
    elif not rep: out["verdict"] = "INELIGIBLE_NO_REPORT"; out["reason"] = f"{len(stim)} stim, no report -> SECONDARY-EVIDENCE only"
    else: out["verdict"] = "ELIGIBLE_FOR_PASS_38_LCC_P3B"; out["reason"] = f"{len(stim)} stim + {len(rep)} report -> proceed"
    h5f.close()
except Exception as e:
    out["error"] = repr(e); out["traceback"] = traceback.format_exc(); out["verdict"] = "INELIGIBLE_EXCEPTION"
print("RESULT_JSON_BEGIN"); print(json.dumps(out, default=str)); print("RESULT_JSON_END")
