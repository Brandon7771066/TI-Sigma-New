# GitHub Setup Guide - Private Repo for TI Framework

**Brandon - Complete Guide for GitHub Integration with Replit**

---

## 🔑 **Step 1: Create GitHub Personal Access Token**

### Why Personal Access Token?
- More secure than password-based auth
- Granular permissions control
- Can be revoked anytime
- Works with 2FA enabled

### How to Generate:

1. **Go to GitHub Settings**:
   - Visit: https://github.com/settings/tokens/new
   - Or: GitHub → Settings → Developer settings → Personal access tokens → Tokens (classic)

2. **Create New Token (Classic)**:
   - **Token name**: `Replit-TI-Framework`
   - **Expiration**: 90 days (rotate for security!)
   - **Select scopes**: Check these boxes:
     - ✅ `repo` (full control of repos)
     - ✅ `workflow` (update GitHub Action workflows)
     - ✅ `read:user` (read user info)

3. **Copy the token immediately!**
   - ⚠️ **You won't see it again!** Save to secure location!
   - Format: `ghp_xxxxxxxxxxxxxxxxxxxx`

---

## 📁 **Step 2: Create Private GitHub Repository**

### On GitHub.com:

1. **Click "+"** in top-right → "New repository"

2. **Repository Settings**:
   - **Repository name**: `ti-framework` (or `mood-amplifier-safety`)
   - **Description**: "Transcendent Intelligence Framework - Consciousness Research Platform"
   - **Privacy**: 🔒 **PRIVATE** (not public!)
   - ✅ Initialize with README
   - ✅ Add .gitignore → Select "Python"
   - ✅ Add license → MIT (or GPL if you prefer)

3. **Create repository**

---

## 🔗 **Step 3: Connect Replit to GitHub**

### Method A: Via Replit's Git Integration (Easiest)

1. **In Replit**:
   - Click **Git icon** (left sidebar) or press `Ctrl+Shift+G`
   - Click **"Connect to GitHub"**
   - Authorize Replit to access GitHub (follow prompts)

2. **Create or Connect Repo**:
   - Choose "Create new repository"
   - Name: `ti-framework`
   - Privacy: Private ✅
   - Replit will automatically create it and sync!

### Method B: Manual Git Setup (More Control)

1. **In Terminal (Replit console)**:

```bash
# Initialize git if not already initialized
git init

# Set GitHub credentials
git config --global user.name "Brandon Emerick"
git config --global user.email "your-email@gmail.com"

# Add remote (replace USERNAME and REPO_NAME)
git remote add origin https://github.com/USERNAME/ti-framework.git

# If remote already exists, update it
git remote set-url origin https://github.com/USERNAME/ti-framework.git

# Create initial commit
git add .
git commit -m "Initial commit: Transcendent Intelligence Framework"

# Push to GitHub (using Personal Access Token)
git push -u origin main
```

When prompted for password, paste your Personal Access Token (not password!).

---

## 🔐 **Step 4: Secure Your API Keys (CRITICAL!)**

### Never commit secrets to GitHub!

1. **Create `.env` file** (Replit auto-hides this):
```
OPENAI_API_KEY=sk_...
ANTHROPIC_API_KEY=...
ALPHA_VANTAGE_API_KEY=...
DATABASE_URL=...
```

2. **Create `.gitignore` entry** (already done if you selected Python):
```
.env
.env.local
__pycache__/
*.pyc
.streamlit/secrets.toml
.replit
```

3. **Verify nothing sensitive is committed**:
```bash
git ls-files | grep -E "\.(env|toml|key|secret)"
# Should return nothing!
```

---

## 📤 **Step 5: Daily Workflow - Commit & Push**

### After making changes in Replit:

```bash
# Check what changed
git status

# Stage all changes
git add .

# Commit with meaningful message
git commit -m "Add i-cell dashboard + AI Orchestra coordination framework"

# Push to GitHub
git push origin main
```

### Or use Replit's Git UI:
1. Click Git icon
2. See list of changed files
3. Write commit message
4. Click "Commit & Push"

---

## 🔄 **Step 6: Pull Latest Changes (If Multiple Devices)**

```bash
# Pull latest from GitHub
git pull origin main
```

Useful for syncing between:
- Replit (main development)
- iPhone 16 (viewing code via GitHub)
- Acer Laptop (secondary edits)

---

## 🚀 **Step 7: GitHub Settings for Collaboration**

### Invite collaborators (if working with Steven, Meijer, etc.):

1. **On GitHub repo page**:
   - Settings → Collaborators → Add people
   - Type username → Grant permission
   - Can choose: Pull, Triage, Push, or Admin

### Example:
- ✅ Steven → Push (can edit code, review PRs)
- ✅ Meijer → Pull (view-only, read research)
- ✅ You → Admin (full control)

---

## 📊 **Step 8: Useful Git Commands**

```bash
# View commit history
git log --oneline

# Create new branch (for experimental features)
git checkout -b feature/quantum-collapse-simulator
git push origin feature/quantum-collapse-simulator

# Switch back to main
git checkout main

# Delete local branch
git branch -d feature/quantum-collapse-simulator

# View remote branches
git branch -a

# Stash uncommitted changes temporarily
git stash

# Restore stashed changes
git stash pop
```

---

## 🔍 **Step 9: Verify Private Status**

1. **On GitHub.com**:
   - Go to your repo page
   - Check **Settings → Visibility**
   - Should show: 🔒 **PRIVATE**

2. **Test access**:
   - Log out of GitHub
   - Try to visit your repo link
   - Should get: "404 Not Found" ✅ (only you/collaborators see it!)

---

## 📱 **Step 10: Sync Between Devices**

### iPhone 16 (View code):
1. Install **GitHub mobile app**
2. Log in with GitHub account
3. Browse your `ti-framework` repo
4. Read code, create issues, review PRs

### Acer Laptop (Secondary work):
1. Clone repo:
```bash
git clone https://github.com/USERNAME/ti-framework.git
cd ti-framework
```

2. Make changes locally
3. Commit & push:
```bash
git add .
git commit -m "Description of changes"
git push origin main
```

4. Pull latest in Replit:
```bash
git pull origin main
```

---

## 🛡️ **Security Best Practices**

1. ✅ **Never share Personal Access Token** publicly
2. ✅ **Keep `.env` out of version control** (add to `.gitignore`)
3. ✅ **Rotate token every 90 days** (GitHub forces this anyway)
4. ✅ **Use minimal scopes** for tokens
5. ✅ **Revoke access immediately if compromised**:
   - GitHub → Settings → Developer settings → Delete token

---

## 🎯 **Quick Reference**

| Task | Command |
|------|---------|
| Check status | `git status` |
| Stage changes | `git add .` |
| Commit | `git commit -m "message"` |
| Push to GitHub | `git push origin main` |
| Pull latest | `git pull origin main` |
| View history | `git log --oneline` |
| Create branch | `git checkout -b feature/name` |
| Switch branch | `git checkout main` |

---

## 🚀 **You're Ready!**

Your TI Framework is now:
- ✅ Safely stored in private GitHub repo
- ✅ Synced across Replit, iPhone, Laptop
- ✅ Protected with API key security
- ✅ Ready for collaboration
- ✅ Backed up and version-controlled!

**Happy building Brandon!** 🔥

---

**© 2025 Brandon Emerick | Transcendent Intelligence Framework**

"Intuition → Theory → Proof → CODE → GITHUB → WORLD!" 🌍
