<#
.SYNOPSIS
  Run pnkzf for n = NMax down to NMin (largest n first, since it takes longest),
  a few at a time, at low CPU priority.

.DESCRIPTION
  For each n:
    <OutDir>\n<n>.txt                      final output, written when the run finishes
    <OutDir>\progress\n<n>.progress.txt    live output of the run (progress updates ~1/s)
    <OutDir>\progress\n<n>.checkpoint.txt  saved search position (every 5 minutes),
                                           deleted once n<n>.txt is written
  <OutDir>\status.txt gives an overview of all runs and is rewritten every PollSeconds.

  Re-running the same command skips every n that already has n<n>.txt and resumes the
  others from their checkpoints, so a reboot or Ctrl+C costs at most ~5 minutes per run.
  Ctrl+C stops the batch and its running pnkzf processes.

.EXAMPLE
  powershell -ExecutionPolicy Bypass -File .\run_all.ps1 -K 4

.EXAMPLE
  powershell -ExecutionPolicy Bypass -File .\run_all.ps1 -K 5 -MaxParallel 5
#>
param(
  [Parameter(Mandatory = $true)][int]$K,
  [int]$NMax = 55,
  [int]$NMin = 48,
  [int]$MaxParallel = 4, # 6 physical cores: leave 2 free for other work
  [ValidateSet('Idle', 'BelowNormal', 'Normal')][string]$Priority = 'BelowNormal',
  [string]$Exe,    # default: pnkzf.exe next to this script
  [string]$OutDir, # default: results\k<K> next to this script
  [int]$PollSeconds = 15
)

$ErrorActionPreference = 'Stop'

# The command that resumes this batch, shown in status.txt.
$ResumeCommand = 'powershell -ExecutionPolicy Bypass -File "{0}"' -f $PSCommandPath
foreach ($bp in $PSBoundParameters.GetEnumerator()) { $ResumeCommand += ' -{0} "{1}"' -f $bp.Key, $bp.Value }

# (PowerShell 5.1 leaves $PSScriptRoot empty inside param defaults, so set these here.)
if (-not $Exe) { $Exe = Join-Path $PSScriptRoot 'pnkzf.exe' }
if (-not $OutDir) { $OutDir = Join-Path $PSScriptRoot "results\k$K" }

$Exe = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($Exe)
$OutDir = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($OutDir)
$ProgressDir = Join-Path $OutDir 'progress'

if (-not (Test-Path $Exe)) {
  throw "pnkzf executable not found: $Exe  (build it with: clang -O3 -march=native -o pnkzf.exe pnkzf.c)"
}
if ($NMin -gt $NMax) { throw "NMin ($NMin) must not exceed NMax ($NMax)" }
if ($MaxParallel -lt 1) { throw "MaxParallel must be at least 1" }

New-Item -ItemType Directory -Force -Path $ProgressDir | Out-Null

# Runs left over from an earlier batch on the same folder (e.g. its window was closed)
# would fight with new ones over the same checkpoint files, so refuse to start.
$exeName = [IO.Path]::GetFileName($Exe)
$others = @(Get-CimInstance Win32_Process -Filter "Name = '$exeName'" -ErrorAction SilentlyContinue)
$ours = @($others | Where-Object { $_.CommandLine -and $_.CommandLine.IndexOf($ProgressDir, [StringComparison]::OrdinalIgnoreCase) -ge 0 })
if ($ours.Count) {
  throw ("$($ours.Count) $exeName run(s) from an earlier batch are still working in $OutDir. " +
    "Stop them first (their checkpoints are kept): Stop-Process -Id $(($ours | ForEach-Object ProcessId) -join ',')")
}
if ($others.Count) {
  Write-Warning "$($others.Count) other $exeName process(es) are running and will compete for CPU."
}

$MaxS = 2 * $K + 2 # pnkzf tests s = 2k+2, 2k+1, ... downward

# Keep Windows from going to sleep while the batch runs.
Add-Type -Namespace Pnkzf -Name Power -MemberDefinition @'
[DllImport("kernel32.dll")] public static extern uint SetThreadExecutionState(uint esFlags);
'@
$ES_CONTINUOUS = [uint32]2147483648 # 0x80000000
$ES_SYSTEM_REQUIRED = [uint32]1

# ---- helpers ----------------------------------------------------------------

function Format-Duration([TimeSpan]$t) {
  if ($t.TotalDays -ge 1) { return '{0}d {1:00}:{2:00}:{3:00}' -f $t.Days, $t.Hours, $t.Minutes, $t.Seconds }
  return '{0:00}:{1:00}:{2:00}' -f [int][math]::Floor($t.TotalHours), $t.Minutes, $t.Seconds
}

function Get-Binomial([int]$m, [int]$r) {
  if ($r -lt 0 -or $r -gt $m) { return 0.0 }
  $x = 1.0
  for ($i = 1; $i -le $r; $i++) { $x = $x * ($m - $r + $i) / $i }
  return $x
}

# Number of candidates pnkzf enumerates for size s (count_candidates() in pnkzf.c).
function Get-Candidates([int]$n, [int]$s) {
  return (Get-Binomial (2 * $n - 1) ($s - 1)) + (Get-Binomial ($n - 1) ($s - 1))
}

# Read a file that pnkzf may still be writing to.
function Read-Shared([string]$path, [long]$offset) {
  $fs = [IO.File]::Open($path, 'Open', 'Read', 'ReadWrite')
  try {
    if ($fs.Length -le $offset) { return '' }
    [void]$fs.Seek($offset, 'Begin')
    $buf = New-Object byte[] ($fs.Length - $offset)
    $read = $fs.Read($buf, 0, $buf.Length)
    return [Text.Encoding]::ASCII.GetString($buf, 0, $read)
  } finally { $fs.Dispose() }
}

# Turn raw output into what a terminal would show: pnkzf redraws its progress
# line with '\r', so only the last '\r'-segment of each line stays visible.
function Convert-TerminalText([string]$raw) {
  $out = foreach ($line in ($raw -split "`r?`n")) {
    $t = $line.TrimEnd("`r")
    $t.Substring($t.LastIndexOf("`r") + 1)
  }
  return ($out -join "`r`n")
}

# Write via a temp file, so a crash never leaves a half-written n<n>.txt behind
# that a resumed batch would mistake for a finished run.
function Write-FileAtomic([string]$path, [string]$text) {
  [IO.File]::WriteAllText("$path.tmp", $text)
  Move-Item -Force -LiteralPath "$path.tmp" -Destination $path
}

# Pull Z and the total time out of a finished run's output.
function Set-ResultInfo($job, [string]$text) {
  if ($text -match 'Z\(P\(\d+,\d+\)\) = (\d+)') { $job.Z = $Matches[1] }
  if ($text -match '\(total time: (\d+)s\)') { $job.Elapsed = [TimeSpan]::FromSeconds([int64]$Matches[1]) }
}

function Start-Run($job) {
  $job.Start = Get-Date
  try {
    $p = Start-Process -FilePath $Exe -ArgumentList $K, $job.N, ('"{0}"' -f $job.CheckpointFile) `
      -WindowStyle Hidden -PassThru -RedirectStandardOutput $job.ProgressFile -RedirectStandardError $job.ErrFile
    $null = $p.Handle # PS 5.1 quirk: needed for ExitCode to be available later
    $p.PriorityClass = [Diagnostics.ProcessPriorityClass]::$Priority
    $job.Proc = $p
    $job.State = 'running'
  } catch {
    $job.State = 'FAILED'
    $job.Note = "could not start: $($_.Exception.Message)"
  }
}

# Read whatever the run printed since the last poll and update its progress.
function Update-Run($job) {
  $now = Get-Date
  $new = Read-Shared $job.ProgressFile $job.Offset
  $job.Offset += $new.Length # ASCII: one char per byte
  $text = $job.Pending + $new

  # Only complete records are final; keep the unterminated tail for next time.
  $cut = [math]::Max($text.LastIndexOf("`r"), $text.LastIndexOf("`n")) + 1
  $complete = $text.Substring(0, $cut)
  $job.Pending = $text.Substring($cut)

  if ($complete -match 'resumed from checkpoint after (\d+)s') {
    $job.EarlierSecs = [int64]$Matches[1]
    $job.Note = 'resumed from checkpoint'
  }

  $sLines = [regex]::Matches($complete, 's = \d+ (WORKS|fails)')
  $after = 0 # progress records before the last "s = " line belong to an earlier s
  if ($sLines.Count) {
    $job.SDone += $sLines.Count
    $job.Count = $null
    $job.BaseCount = $null # new s: restart the speed measurement
    $after = $sLines[$sLines.Count - 1].Index
  }
  $m = [regex]::Matches($text.Substring($after), '(\d+) \(\d+\.\d%\)\.\.\.')
  if ($m.Count) {
    $job.Count = [int64]$m[$m.Count - 1].Groups[1].Value
    if ($null -eq $job.BaseCount) { $job.BaseCount = $job.Count; $job.BaseTime = $now }
  }
  $job.Elapsed = [TimeSpan]::FromSeconds($job.EarlierSecs) + ($now - $job.Start)

  # ETA for the current s, from the speed measured since its first progress line in this run.
  $job.Eta = $null
  if ($null -ne $job.Count -and $job.Count -gt $job.BaseCount) {
    $rate = ($job.Count - $job.BaseCount) / ($now - $job.BaseTime).TotalSeconds
    $left = (Get-Candidates $job.N ($MaxS - $job.SDone)) - $job.Count
    $job.Eta = [TimeSpan]::FromSeconds([math]::Min(1e10, [math]::Max(0, $left / $rate)))
  }

  if ($job.Proc.HasExited) { Complete-Run $job }
}

function Complete-Run($job) {
  $code = $job.Proc.ExitCode
  $text = Convert-TerminalText (Read-Shared $job.ProgressFile 0)
  $job.Eta = $null
  if ($code -eq 0) {
    Write-FileAtomic $job.ResultFile $text
    Remove-Item -LiteralPath $job.CheckpointFile, "$($job.CheckpointFile).tmp" -ErrorAction SilentlyContinue
    $job.State = 'done'
    $job.Note = ''
    Set-ResultInfo $job $text
  } else {
    Write-FileAtomic (Join-Path $OutDir ('n{0}.failed.txt' -f $job.N)) $text
    $job.State = 'FAILED'
    $job.Note = "exit code $code, see n$($job.N).failed.txt"
  }
}

function Write-Status {
  $running = @($jobs | Where-Object { $_.State -eq 'running' }).Count
  $row = '{0,3}  {1,-8} {2,3} {3,20} {4,7}  {5,13}  {6,13}  {7,3}  {8}'
  $lines = @(
    "pnkzf batch   k = $K   n = $NMax..$NMin   parallel = $MaxParallel   priority = $Priority"
    "updated $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')   running: $running   queued: $($queue.Count)"
    ''
    ($row -f 'n', 'state', 's', 'candidates', 'pct', 'elapsed', 'ETA (this s)', 'Z', '')
    ('-' * 100)
  )
  foreach ($job in $jobs) {
    $s = $pct = $count = $eta = $elapsed = ''
    if ($job.State -eq 'running') {
      $s = $MaxS - $job.SDone
      if ($null -ne $job.Count) {
        $count = '{0:N0}' -f $job.Count
        $pct = '{0:0.00}%' -f (100 * $job.Count / (Get-Candidates $job.N $s))
      }
      if ($job.Eta) { $eta = Format-Duration $job.Eta }
    }
    if ($job.Elapsed) { $elapsed = Format-Duration $job.Elapsed }
    $lines += $row -f $job.N, $job.State, $s, $count, $pct, $elapsed, $eta, $job.Z, $job.Note
  }
  $lines += ''
  $lines += 'ETA (this s) = time left if the current size s is searched to 100%, at the speed measured since'
  $lines += 'this run (re)started. A size s that works stops early; the last s (the one that fails) runs to 100%.'
  $lines += "Live output: $ProgressDir\n<n>.progress.txt"
  $lines += "To resume after a reboot or Ctrl+C:  $ResumeCommand"

  $text = $lines -join "`r`n"
  try { [IO.File]::WriteAllText((Join-Path $OutDir 'status.txt'), $text + "`r`n") } catch { } # retry next poll
  try { Clear-Host } catch { }
  Write-Host $text
}

# ---- main -------------------------------------------------------------------

$jobs = New-Object 'System.Collections.Generic.List[object]'  # in run order: largest n first
$queue = New-Object 'System.Collections.Generic.Queue[object]'
for ($n = $NMax; $n -ge $NMin; $n--) {
  $job = @{
    N = $n; State = 'queued'; Proc = $null; Note = ''; Z = ''
    ProgressFile = Join-Path $ProgressDir ('n{0}.progress.txt' -f $n)
    CheckpointFile = Join-Path $ProgressDir ('n{0}.checkpoint.txt' -f $n)
    ErrFile = Join-Path $ProgressDir ('n{0}.err.txt' -f $n)
    ResultFile = Join-Path $OutDir ('n{0}.txt' -f $n)
    Start = $null; Elapsed = $null; EarlierSecs = 0L; Offset = 0L; Pending = ''
    SDone = 0; Count = $null; BaseCount = $null; BaseTime = $null; Eta = $null
  }
  $jobs.Add($job)
  if (Test-Path -LiteralPath $job.ResultFile) {
    $job.State = 'done'
    $job.Note = '(earlier run)'
    Set-ResultInfo $job ([IO.File]::ReadAllText($job.ResultFile))
  } else {
    $queue.Enqueue($job)
  }
}

[void][Pnkzf.Power]::SetThreadExecutionState($ES_CONTINUOUS -bor $ES_SYSTEM_REQUIRED)
try {
  while ($true) {
    foreach ($job in @($jobs | Where-Object { $_.State -eq 'running' })) { Update-Run $job }

    while ($queue.Count -and @($jobs | Where-Object { $_.State -eq 'running' }).Count -lt $MaxParallel) {
      Start-Run $queue.Dequeue()
    }

    Write-Status
    if (-not $queue.Count -and -not @($jobs | Where-Object { $_.State -eq 'running' }).Count) { break }
    Start-Sleep -Seconds $PollSeconds
  }
} finally {
  # Reached on normal exit and on Ctrl+C: don't leave hidden pnkzf processes behind.
  foreach ($job in @($jobs | Where-Object { $_.State -eq 'running' })) {
    if (-not $job.Proc.HasExited) { Stop-Process -Id $job.Proc.Id -Force -ErrorAction SilentlyContinue }
    $job.State = 'stopped'
    $job.Note = 'resumes from its checkpoint on the next run'
  }
  [void][Pnkzf.Power]::SetThreadExecutionState($ES_CONTINUOUS)
  try { Write-Status } catch { }
}
