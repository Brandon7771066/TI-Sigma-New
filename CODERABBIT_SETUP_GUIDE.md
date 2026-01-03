# CodeRabbit Setup Guide for TI Framework

## What is CodeRabbit?
CodeRabbit is an AI-powered code review tool that automatically reviews pull requests on GitHub. It catches bugs, security issues, and style problems before human reviewers see them.

## Why Use CodeRabbit Daily?
- **Catch bugs early**: AI reviews every commit for potential issues
- **Security scanning**: Automatic detection of vulnerabilities
- **Code quality**: Enforces consistent style and best practices
- **Learning**: Explains detected issues so you understand the fixes

## Setup Instructions (5 Minutes)

### Step 1: Install from GitHub Marketplace
1. Go to [GitHub Marketplace](https://github.com/marketplace/coderabbitai)
2. Search for "CodeRabbit"
3. Click "Set up a plan"
4. Choose **Free tier** (sufficient for our project)
5. Click "Install & Authorize"

### Step 2: Authorize Permissions
GitHub will ask for:
- Read-only access to organizations, teams, and email
- Click "Authorize coderabbitai"

### Step 3: Select Repository
- Choose "Only select repositories"
- Select the TI Framework repository
- Click "Install & Authorize"

## Configuration (Optional)

Create a `.coderabbit.yaml` file in the repo root:

```yaml
reviews:
  profile: "assertive"
  request_changes_workflow: true
  high_level_summary: true
  poem: false

language: "en-US"

# TI Framework specific rules
review_instructions:
  - "Ensure all TI algorithms include empirical validation references"
  - "Check for proper GILE score bounds (-0.666 to 0.333)"
  - "Verify LCC calculations use only public market data"
  - "Flag any hardcoded API keys or secrets"
  - "Ensure hypercomputer claims include appropriate disclaimers"
  - "Check tralsebit algebra follows correct Φ/Ψ propagation rules"
```

## Daily Usage Workflow

1. **Create a branch** for your feature
2. **Make your changes** and commit
3. **Open a pull request** on GitHub
4. **Wait 1-2 minutes** for CodeRabbit review
5. **Review AI comments** - click "Commit Suggestion" to apply fixes
6. **Merge** after addressing all issues

## Example Daily Review Schedule

| Time | Action |
|------|--------|
| Morning | Create PR with overnight changes |
| 10 AM | Review CodeRabbit feedback |
| Afternoon | Push additional commits |
| 5 PM | Final CodeRabbit review before merge |

## Cost

- **Free tier**: Unlimited for open-source, limited for private repos
- **Pro tier**: ~$30/user/month with advanced features

## Benefits for TI Framework

1. **Algorithm Validation**: Catches math errors in GILE calculations
2. **Security**: Prevents accidental exposure of API keys
3. **Documentation**: Ensures proper disclaimers on hypercomputer claims
4. **Consistency**: Enforces TI Framework coding standards
5. **Learning**: Helps understand Python best practices

## Troubleshooting

**Q: CodeRabbit isn't reviewing my PR**
A: Check that the repository is authorized in GitHub Settings > Applications

**Q: Too many nitpicky comments?**
A: Adjust the `profile` setting to "chill" in `.coderabbit.yaml`

**Q: Want more detailed reviews?**
A: Use the chat feature - tag @coderabbitai in any PR comment

---

*Setup created for BlissGene Therapeutics / TI Framework*
*Author: Brandon Emerick*
*Date: November 30, 2025*
