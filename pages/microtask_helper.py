"""
Microtask Helper - Streamlit Page
Paste task descriptions to get instant DO IT / SKIP recommendations
"""

import streamlit as st
import sys
sys.path.append('..')
from microtask_helper import evaluate_task, format_evaluation, TaskEvaluation

st.set_page_config(page_title="Microtask Helper", page_icon="💰", layout="wide")

st.title("💰 Microtask Evaluation Helper")
st.markdown("**Paste a task description → Get instant DO IT / SKIP verdict**")

st.divider()

col1, col2 = st.columns([2, 1])

with col1:
    task_text = st.text_area(
        "📋 Paste Task Description Here",
        height=300,
        placeholder="""Paste the full task instructions from Toloka or Clickworker here...

Example:
"Evaluate AI Response Quality - You will be shown a question and two AI-generated responses. Choose which response is better based on accuracy, helpfulness, and clarity."
"""
    )
    
    col_pay, col_time = st.columns(2)
    with col_pay:
        pay_amount = st.number_input("💵 Pay per task ($)", min_value=0.0, value=0.0, step=0.01, format="%.2f")
    with col_time:
        time_minutes = st.number_input("⏱️ Est. minutes per task", min_value=0.0, value=0.0, step=0.5)
    
    evaluate_btn = st.button("🔍 Evaluate Task", type="primary", use_container_width=True)

with col2:
    st.markdown("### 📊 Quick Reference")
    st.markdown("""
    **✅ DO THESE (High Pay):**
    - Evaluate response
    - Choose better answer  
    - Rate relevance
    - Fact-check answer
    - Side-by-side comparison
    
    **❌ SKIP THESE (Tonight):**
    - Audio transcription
    - Long surveys
    - Image bounding boxes
    - Training/qualification
    - Vague instructions
    
    **⏱️ 90-Second Rule:**
    If a task takes >90 sec, SKIP IT
    """)

st.divider()

if evaluate_btn and task_text.strip():
    pay = pay_amount if pay_amount > 0 else None
    time_est = time_minutes if time_minutes > 0 else None
    
    evaluation = evaluate_task(task_text, pay, time_est)
    
    if evaluation.verdict == "DO IT":
        st.success(f"## ✅ VERDICT: DO IT")
    elif evaluation.verdict == "SKIP":
        st.error(f"## ❌ VERDICT: SKIP")
    else:
        st.warning(f"## ⚠️ VERDICT: MAYBE")
    
    col_a, col_b = st.columns(2)
    with col_a:
        st.metric("💰 Estimated Pay", evaluation.estimated_pay_per_hour)
    with col_b:
        st.metric("⏱️ Time per Task", evaluation.time_estimate)
    
    st.markdown("### 📋 Recommended Approach")
    st.code(evaluation.approach, language=None)
    
    if evaluation.warnings:
        st.markdown("### ⚠️ Warnings")
        for w in evaluation.warnings:
            st.warning(w)

elif evaluate_btn:
    st.warning("Please paste a task description first!")

st.divider()

st.markdown("### 🎯 Tonight's Goal")
st.info("""
**Target: $5-$15 in your first session**

1. Open Toloka → Do 1-2 high-rating evaluation tasks
2. Switch to Clickworker → Do 1 batch  
3. Log out

**Speed > Perfection** - Get rhythm going, don't overthink!
""")

with st.expander("💡 Pro Tips for Higher Acceptance"):
    st.markdown("""
    **For Comparison Tasks:**
    - More direct = better
    - More accurate = better
    - Simpler = better (when tied)
    - NO creativity - reward boring correctness
    
    **For Rating Tasks:**
    - Follow the rubric EXACTLY
    - Use middle ratings when unsure
    - Don't overthink edge cases
    
    **General Rules:**
    - First 5-10 tasks: Go slower to learn patterns
    - After that: Build speed
    - If frustrated: Switch platforms or take break
    - Track what task types you're good at
    """)

with st.expander("📈 Scaling Up Later"):
    st.markdown("""
    Once you're consistently earning:
    
    **Week 1-2:** Build reputation on both platforms
    - Focus on acceptance rate
    - Learn which tasks you're fastest at
    
    **Week 3+:** Optimize
    - Do only your highest $/hr tasks
    - Consider adding Prolific (higher pay, less volume)
    - Track earnings in spreadsheet
    
    **Automation (Future):**
    - Task notification alerts
    - Auto-filter by pay rate
    - Batch task selection
    
    We can build this later once you know which tasks work for you!
    """)
