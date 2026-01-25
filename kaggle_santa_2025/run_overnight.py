#!/usr/bin/env python
"""Wrapper to run overnight solver - use as workflow"""
import sys
import os
os.chdir('/home/runner/workspace/kaggle_santa_2025')
sys.path.insert(0, '/home/runner/workspace/kaggle_santa_2025')

from ti_overnight_runner import multi_run
multi_run(num_runs=10)
