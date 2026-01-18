"""
GitHub Code Proofreader
=======================
AI-powered code review using GitHub integration.
Analyzes our TI codebase for quality, bugs, and improvements.
"""

import streamlit as st
import os
import requests
from datetime import datetime

st.set_page_config(page_title="Code Proofreader", page_icon="📝", layout="wide")

def get_github_token():
    """Get GitHub access token from Replit connector."""
    try:
        hostname = os.environ.get('REPLIT_CONNECTORS_HOSTNAME')
        repl_identity = os.environ.get('REPL_IDENTITY')
        web_repl_renewal = os.environ.get('WEB_REPL_RENEWAL')
        
        if repl_identity:
            x_replit_token = f'repl {repl_identity}'
        elif web_repl_renewal:
            x_replit_token = f'depl {web_repl_renewal}'
        else:
            return None
        
        response = requests.get(
            f'https://{hostname}/api/v2/connection?include_secrets=true&connector_names=github',
            headers={
                'Accept': 'application/json',
                'X_REPLIT_TOKEN': x_replit_token
            }
        )
        data = response.json()
        connection = data.get('items', [{}])[0]
        settings = connection.get('settings', {})
        
        token = settings.get('access_token') or settings.get('oauth', {}).get('credentials', {}).get('access_token')
        return token
    except Exception as e:
        st.error(f"GitHub connection error: {e}")
        return None

def get_repos(token):
    """Fetch user's repositories."""
    try:
        response = requests.get(
            'https://api.github.com/user/repos',
            headers={
                'Authorization': f'token {token}',
                'Accept': 'application/vnd.github.v3+json'
            },
            params={'per_page': 100, 'sort': 'updated'}
        )
        return response.json()
    except Exception as e:
        return []

def get_repo_files(token, owner, repo, path=""):
    """Get files in a repository."""
    try:
        response = requests.get(
            f'https://api.github.com/repos/{owner}/{repo}/contents/{path}',
            headers={
                'Authorization': f'token {token}',
                'Accept': 'application/vnd.github.v3+json'
            }
        )
        return response.json()
    except Exception as e:
        return []

def get_file_content(token, owner, repo, path):
    """Get content of a specific file."""
    try:
        response = requests.get(
            f'https://api.github.com/repos/{owner}/{repo}/contents/{path}',
            headers={
                'Authorization': f'token {token}',
                'Accept': 'application/vnd.github.v3+json'
            }
        )
        data = response.json()
        if 'content' in data:
            import base64
            content = base64.b64decode(data['content']).decode('utf-8')
            return content
        return None
    except Exception as e:
        return None

def analyze_code_with_ai(code, filename):
    """Use Claude to analyze code quality."""
    try:
        import anthropic
        client = anthropic.Anthropic()
        
        prompt = f"""Analyze this code file and provide a brief, actionable code review.
Focus on:
1. Potential bugs or errors
2. Code quality improvements
3. Security concerns
4. Documentation gaps
5. Best practices

File: {filename}

```
{code[:8000]}
```

Provide your review in this format:
## Summary
(1-2 sentences)

## Issues Found
- Issue 1
- Issue 2

## Suggestions
- Suggestion 1
- Suggestion 2

## Quality Score
X/10

Keep it concise and actionable."""

        message = client.messages.create(
            model="claude-sonnet-4-20250514",
            max_tokens=1000,
            messages=[{"role": "user", "content": prompt}]
        )
        block = message.content[0]
        return getattr(block, 'text', str(block))
    except Exception as e:
        return f"Analysis error: {e}"

def analyze_local_file(filepath):
    """Analyze a local file."""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        return analyze_code_with_ai(content, filepath)
    except Exception as e:
        return f"Error reading file: {e}"

st.title("📝 GitHub Code Proofreader")
st.write("AI-powered code review for quality assurance and bug detection.")

tab1, tab2 = st.tabs(["🔗 GitHub Repository", "📁 Local Files"])

with tab1:
    token = get_github_token()
    
    if token:
        st.success("Connected to GitHub!")
        
        repos = get_repos(token)
        if repos and isinstance(repos, list):
            repo_names = [f"{r['owner']['login']}/{r['name']}" for r in repos if isinstance(r, dict)]
            
            selected_repo = st.selectbox("Select Repository", repo_names)
            
            if selected_repo:
                owner, repo = selected_repo.split('/')
                
                files = get_repo_files(token, owner, repo)
                
                code_extensions = {'.py', '.js', '.ts', '.jsx', '.tsx', '.go', '.rs', '.java', '.cpp', '.c', '.h'}
                
                if isinstance(files, list):
                    code_files = [
                        f['path'] for f in files 
                        if isinstance(f, dict) and f.get('type') == 'file'
                        and any(f['name'].endswith(ext) for ext in code_extensions)
                    ]
                    
                    if code_files:
                        selected_file = st.selectbox("Select File to Review", code_files)
                        
                        if selected_file and st.button("🔍 Analyze Code", type="primary"):
                            with st.spinner(f"Analyzing {selected_file}..."):
                                content = get_file_content(token, owner, repo, selected_file)
                                if content:
                                    ext = selected_file.split('.')[-1] if '.' in selected_file else 'txt'
                                    with st.expander("📄 File Content", expanded=False):
                                        st.code(content[:3000], language=ext)
                                    
                                    st.write("---")
                                    st.subheader("🤖 AI Review")
                                    review = analyze_code_with_ai(content, selected_file)
                                    st.markdown(review)
                                else:
                                    st.error("Could not fetch file content")
                    else:
                        st.info("No code files found in repository root. Try browsing subdirectories.")
                        
                        folders = [f['path'] for f in files if isinstance(f, dict) and f.get('type') == 'dir']
                        if folders:
                            selected_folder = st.selectbox("Browse Folder", folders)
                            if selected_folder and st.button("📂 Open Folder"):
                                sub_files = get_repo_files(token, owner, repo, str(selected_folder))
                                if isinstance(sub_files, list):
                                    for f in sub_files:
                                        if isinstance(f, dict):
                                            st.write(f"- {f.get('name', 'unknown')}")
        else:
            st.warning("No repositories found or API rate limited.")
    else:
        st.warning("GitHub not connected. Please set up the GitHub integration first.")

with tab2:
    st.subheader("Review Local Project Files")
    
    common_files = []
    for root, dirs, files in os.walk('.'):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['node_modules', '__pycache__', 'venv', '.git']]
        for f in files:
            if f.endswith(('.py', '.js', '.ts')):
                path = os.path.join(root, f)
                if len(path) < 100:
                    common_files.append(path)
        if len(common_files) > 50:
            break
    
    if common_files:
        selected_local = st.selectbox("Select Local File", sorted(common_files)[:50])
        
        if selected_local and st.button("🔍 Analyze Local File", type="primary", key="local_analyze"):
            filepath = str(selected_local)
            with st.spinner(f"Analyzing {filepath}..."):
                try:
                    with open(filepath, 'r') as f:
                        content = f.read()
                    
                    with st.expander("📄 File Content", expanded=False):
                        lang = 'python' if filepath.endswith('.py') else 'javascript'
                        st.code(content[:3000], language=lang)
                    
                    st.write("---")
                    st.subheader("🤖 AI Review")
                    review = analyze_code_with_ai(content, selected_local)
                    st.markdown(review)
                except Exception as e:
                    st.error(f"Error: {e}")
    else:
        st.info("No code files found in current directory.")

st.write("---")
with st.expander("ℹ️ How It Works"):
    st.markdown("""
    ### GitHub Code Proofreader
    
    This tool uses AI (Claude) to review your code for:
    
    - **Bugs & Errors**: Logic issues, type mismatches, edge cases
    - **Security**: Vulnerabilities, exposed secrets, injection risks
    - **Quality**: Code style, naming, structure, complexity
    - **Documentation**: Missing comments, unclear functions
    - **Best Practices**: Framework patterns, performance, maintainability
    
    ### Usage
    1. **GitHub Tab**: Connect to your repositories and select files
    2. **Local Tab**: Review files in this Replit project
    
    Each review provides a quality score and actionable suggestions.
    """)
