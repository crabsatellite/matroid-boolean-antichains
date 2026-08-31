$ErrorActionPreference = "Stop"
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$PaperDir = Join-Path $ProjectRoot "paper"
$OutputDir = Join-Path $ProjectRoot "output"
$Main = "matroid_boolean_antichains"
New-Item -ItemType Directory -Force -Path $OutputDir | Out-Null
Push-Location $PaperDir
try {
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory $OutputDir "$Main.tex"
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  bibtex (Join-Path $OutputDir $Main)
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory $OutputDir "$Main.tex"
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory $OutputDir "$Main.tex"
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
} finally {
  Pop-Location
}
Write-Output "paper_build=passed"
