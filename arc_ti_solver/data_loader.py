"""
ARC-AGI Dataset Loader
Handles local files (downloaded from Kaggle/GitHub) and GitHub fetch.
"""

import json
import os
import urllib.request
from pathlib import Path
from typing import Optional

ARC_GITHUB_BASE = "https://raw.githubusercontent.com/fchollet/ARC-AGI/master/data"
DATA_DIR = Path(__file__).parent / "data"


def download_arc_dataset(split: str = "training") -> Path:
    """
    Download ARC tasks from GitHub if not already present.
    split: 'training' | 'evaluation'
    Returns path to the directory containing task JSON files.
    """
    target_dir = DATA_DIR / split
    target_dir.mkdir(parents=True, exist_ok=True)

    index_url = f"{ARC_GITHUB_BASE}/{split}/"
    print(f"Fetching ARC {split} task list...")

    manifests = []
    try:
        with urllib.request.urlopen(
            f"https://api.github.com/repos/fchollet/ARC-AGI/contents/data/{split}"
        ) as resp:
            items = json.loads(resp.read())
            manifests = [item["name"] for item in items if item["name"].endswith(".json")]
    except Exception as e:
        print(f"  Warning: could not fetch manifest ({e})")
        return target_dir

    existing = {p.name for p in target_dir.glob("*.json")}
    new_tasks = [m for m in manifests if m not in existing]

    if not new_tasks:
        print(f"  {len(manifests)} tasks already downloaded.")
        return target_dir

    print(f"  Downloading {len(new_tasks)} tasks...")
    for i, name in enumerate(new_tasks):
        url = f"{ARC_GITHUB_BASE}/{split}/{name}"
        try:
            with urllib.request.urlopen(url) as resp:
                data = resp.read()
            (target_dir / name).write_bytes(data)
            if (i + 1) % 50 == 0:
                print(f"  {i + 1}/{len(new_tasks)} downloaded...")
        except Exception as e:
            print(f"  Failed: {name} ({e})")

    print(f"  Done. {len(list(target_dir.glob('*.json')))} tasks available.")
    return target_dir


def load_task(task_path: Path) -> dict:
    """Load a single ARC task JSON."""
    with open(task_path) as f:
        return json.load(f)


def load_all_tasks(split: str = "training", local_dir: Optional[str] = None) -> dict:
    """
    Load all tasks for a split.
    Returns dict: {task_id: task_dict}
    """
    if local_dir:
        task_dir = Path(local_dir)
    else:
        task_dir = DATA_DIR / split
        if not task_dir.exists() or not list(task_dir.glob("*.json")):
            task_dir = download_arc_dataset(split)

    tasks = {}
    for path in sorted(task_dir.glob("*.json")):
        task_id = path.stem
        tasks[task_id] = load_task(path)

    print(f"Loaded {len(tasks)} ARC {split} tasks.")
    return tasks


def grid_dims(grid: list) -> tuple:
    """Return (rows, cols) of a grid."""
    return len(grid), len(grid[0]) if grid else 0


def grid_colors(grid: list) -> set:
    """Return set of unique colors in a grid."""
    return {cell for row in grid for cell in row}


def task_summary(task: dict) -> dict:
    """Quick statistics about a task."""
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])
    summary = {
        "n_train": len(train_pairs),
        "n_test": len(test_pairs),
        "train_dims": [(grid_dims(p["input"]), grid_dims(p["output"])) for p in train_pairs],
        "input_colors": sorted(grid_colors(train_pairs[0]["input"])) if train_pairs else [],
        "output_colors": sorted(grid_colors(train_pairs[0]["output"])) if train_pairs else [],
        "size_preserved": all(
            grid_dims(p["input"]) == grid_dims(p["output"]) for p in train_pairs
        ),
    }
    return summary
