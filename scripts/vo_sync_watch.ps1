# vo_sync_watch.ps1 -- automatic counterpart-side vo trust-cache sync (Windows/PowerShell form; the mac side uses vo_sync_watch.sh)
#
# Mission: a resident scheduled task on the Windows runner side -- once a CI run pushed by the counterpart (mac) side is fully green, automatically download
# the vo-trust-cache-macos artifact and mirror-merge it into the Windows local trust-cache tree
# (D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo) -- the next CI
# "Seed trust cache" step then seeds from fingerprints and hits SKIP, giving automatic two-machine certification handoff.
#
# One-time install (administrator or per-user scheduled task, polling every 2 minutes):
#   schtasks /Create /TN "vo_sync_watch" /SC MINUTE /MO 2 /TR ^
#     "pwsh -File D:\actions-runner\scripts\vo_sync_watch.ps1" /F
# Parameters (defaults at the top of the script are editable):
#   $Repo / $Artifact / $CacheDir / $StateFile
# token: obtained automatically via git credential (same source as push).

$Repo      = "hy7pc8gfmf-dotcom/ConstructiveWorld-Main"
$Artifact  = "vo-trust-cache-macos"
$CacheDir  = "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo"
$StateFile = "D:\actions-runner\.vo_sync_last_run"

function Get-Token {
  $out = "protocol=https`nhost=github.com`n" | git credential fill 2>$null
  ($out | Select-String '^password=' ) -replace '^password=', ''
}

$Last = 0
if (Test-Path $StateFile) { $Last = [long](Get-Content $StateFile -ErrorAction SilentlyContinue) }
Write-Output "vo_sync_watch: repo=$Repo artifact=$Artifact cache=$CacheDir last_run=$Last"

while ($true) {
  try {
    $Token = Get-Token
    $H = @{ }
    if ($Token) { $H["Authorization"] = "token $Token" }
    # 1. latest green run
    $runs = Invoke-RestMethod -Headers $H -TimeoutSec 30 `
      "https://api.github.com/repos/$Repo/actions/runs?branch=main&status=success&per_page=1"
    $RunId = 0
    if ($runs.workflow_runs.Count -gt 0) { $RunId = [long]$runs.workflow_runs[0].id }
    if ($RunId -gt $Last) {
      Write-Output "vo_sync_watch: new green run $RunId — syncing $Artifact"
      # 2. locate the artifact
      $arts = Invoke-RestMethod -Headers $H -TimeoutSec 30 `
        "https://api.github.com/repos/$Repo/actions/runs/$RunId/artifacts?per_page=50"
      $aid = ($arts.artifacts | Where-Object { $_.name -eq $Artifact } | Select-Object -First 1).id
      if ($aid -and $Token) {
        # 3. download + mirror merge
        $tmp = Join-Path $env:TEMP ("vo_sync_" + [guid]::NewGuid().ToString("N"))
        New-Item -ItemType Directory -Path $tmp -Force | Out-Null
        $zip = Join-Path $tmp "vo.zip"
        Invoke-WebRequest -Headers @{ Authorization = "token $Token" } -TimeoutSec 600 `
          -Uri "https://api.github.com/repos/$Repo/actions/artifacts/$aid/zip" -OutFile $zip
        Expand-Archive -Path $zip -DestinationPath (Join-Path $tmp "vo") -Force
        $vos = Get-ChildItem -Path (Join-Path $tmp "vo") -Filter *.vo -Recurse
        Get-ChildItem -Path $CacheDir -Filter *.vo -File -ErrorAction SilentlyContinue | Remove-Item -Force
        $vos | ForEach-Object { Copy-Item $_.FullName $CacheDir -Force }
        Write-Output "vo_sync_watch: run $RunId synced $($vos.Count) .vo -> $CacheDir"
        Set-Content -Path $StateFile -Value $RunId
        Remove-Item -Recurse -Force $tmp
      }
      else {
        Write-Output "vo_sync_watch: run $RunId has no $Artifact — marking seen"
        Set-Content -Path $StateFile -Value $RunId
      }
      $Last = $RunId
    }
  }
  catch {
    Write-Output "vo_sync_watch: poll error: $($_.Exception.Message) — retry next cycle"
  }
  Start-Sleep -Seconds 60
}
