"""Semantic Versioning Rules and Registry Version."""

REGISTRY_VERSION = "1.0.0"

class SemanticVersion:
    def __init__(self, major: int = 1, minor: int = 0, patch: int = 0):
        self.major = major
        self.minor = minor
        self.patch = patch

    def __str__(self):
        return f"{self.major}.{self.minor}.{self.patch}"
