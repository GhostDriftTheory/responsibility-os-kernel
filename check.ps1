$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

if (-not (Test-Path -LiteralPath "ResponsibilityOS.lean")) {
  throw "ResponsibilityOS.lean was not found in the repository root."
}

if (-not (Test-Path -LiteralPath "lakefile.lean")) {
  throw "lakefile.lean was not found in the repository root."
}

if (-not (Test-Path -LiteralPath "lean-toolchain")) {
  throw "lean-toolchain was not found in the repository root."
}

$requiredLeanNames = @(
  "structure ObservationPolicy",
  "def PreservesPolicy",
  "def CompletePolicy",
  "theorem preserves_complete_policy_iff_faithful",
  "theorem complete_inspectability_requires_faithful",
  "theorem nonfaithful_view_not_completely_inspectable",
  "def tracePolicy",
  "theorem trace_policy_relevant",
  "theorem U_does_not_preserve_trace_policy",
  "theorem trace_policy_distinction_is_relevant",
  "theorem operational_view_does_not_preserve_trace_policy",
  "theorem forgetting_responsibility_layer_can_collapse_distinctions"
)

foreach ($name in $requiredLeanNames) {
  if (-not (Select-String -LiteralPath "ResponsibilityOS.lean" -SimpleMatch $name -Quiet)) {
    throw "Required Lean declaration was not found: $name"
  }
}

$forbiddenLeanText = @(
  "sorry",
  "import AIAssurance",
  "Mathlib.CategoryTheory.Quotient",
  "Mathlib.CategoryTheory.Yoneda",
  "Functor.ReflectsIso",
  "def functorRel",
  "GovernanceQuotient",
  "yoneda_reflects_iso"
)

foreach ($text in $forbiddenLeanText) {
  if (Select-String -LiteralPath "ResponsibilityOS.lean" -SimpleMatch $text -Quiet) {
    throw "Forbidden Lean text was found: $text"
  }
}

if ($env:GITHUB_ACTIONS -eq "true") {
  lake exe cache get
  if ($LASTEXITCODE -ne 0) {
    throw "Mathlib cache download failed in GitHub Actions."
  }
} else {
  Write-Host "Skipping Mathlib cache download outside GitHub Actions."
}

lake env lean ResponsibilityOS.lean
if ($LASTEXITCODE -ne 0) {
  throw "Lean verification failed."
}

$requiredReadmeText = @(
  "If inspectable governance is formalized as preservation of policy-relevant responsibility distinctions",
  "The connection to any concrete governance deployment requires additional interpretation beyond this formalization.",
  "ResponsibilityOS.ObservationPolicy",
  "ResponsibilityOS.PreservesPolicy",
  "ResponsibilityOS.CollapseCounterexample.tracePolicy",
  "ResponsibilityOS.operational_view_does_not_preserve_trace_policy"
)

foreach ($text in $requiredReadmeText) {
  if (-not (Select-String -LiteralPath "README.md" -SimpleMatch $text -Quiet)) {
    throw "Required README text was not found: $text"
  }
}

Write-Host "Successful verification returns to the prompt with no errors."
