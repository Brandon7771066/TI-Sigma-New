#!/bin/bash
# Push TI Framework to GitHub
# Run this in the Shell tab

echo "==================================="
echo "Push to GitHub - TI Framework"
echo "==================================="

# Set up git config (if needed)
git config user.email "Brandon7771066@users.noreply.github.com"
git config user.name "Brandon7771066"

# Add the remote (if not already added)
git remote add origin https://github.com/Brandon7771066/TI-Framework-BlissGene.git 2>/dev/null || \
git remote set-url origin https://github.com/Brandon7771066/TI-Framework-BlissGene.git

echo ""
echo "Remote configured: https://github.com/Brandon7771066/TI-Framework-BlissGene.git"
echo ""
echo "To push your code, run these commands in the Shell:"
echo ""
echo "  git add ."
echo "  git commit -m 'Initial commit - TI Framework Platform'"
echo "  git push -u origin main"
echo ""
echo "You may be prompted for GitHub credentials."
echo "==================================="
