#!/usr/bin/env bash
set -euo pipefail

verification_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$verification_dir"

lake update
lake exe cache get
lake build PrimeGaps186
lake build IntegratedBridge
lake env lean IntegratedBridgeAudit.lean
