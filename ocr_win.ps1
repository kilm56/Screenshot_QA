param(
    [Parameter(Mandatory = $true)][string]$Path,
    [string]$OutFile = "",
    [string]$Language = "zh-Hans-CN"
)

# Windows built-in OCR helper. Writes a JSON result to OutFile (UTF-8).
# Keep this file ASCII-only: Windows PowerShell 5.1 parses BOM-less scripts as ANSI,
# which corrupts non-ASCII comments. The Python side maps error codes to Chinese text.

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

function Write-Result {
    param($Payload)
    $json = $Payload | ConvertTo-Json -Depth 6 -Compress
    if ($OutFile -ne "") {
        [System.IO.File]::WriteAllText($OutFile, $json, (New-Object System.Text.UTF8Encoding($false)))
    }
    else {
        [Console]::OutputEncoding = New-Object System.Text.UTF8Encoding($false)
        [Console]::Out.Write($json)
    }
}

function Exit-WithError {
    param([string]$Code, [string]$Detail)
    Write-Result @{ ok = $false; error_code = $Code; detail = $Detail }
    exit 0
}

try {
    Add-Type -AssemblyName System.Runtime.WindowsRuntime
    $null = [Windows.Storage.Streams.IRandomAccessStream, Windows.Storage, ContentType = WindowsRuntime]
    $null = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Graphics.Imaging, ContentType = WindowsRuntime]
    $null = [Windows.Graphics.Imaging.SoftwareBitmap, Windows.Graphics.Imaging, ContentType = WindowsRuntime]
    $null = [Windows.Media.Ocr.OcrEngine, Windows.Media.Ocr, ContentType = WindowsRuntime]
    $null = [Windows.Globalization.Language, Windows.Globalization, ContentType = WindowsRuntime]

    $asTaskGeneric = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
            $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and
            $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1'
        })[0]

    function Await($WinRtTask, $ResultType) {
        $asTask = $asTaskGeneric.MakeGenericMethod($ResultType)
        $netTask = $asTask.Invoke($null, @($WinRtTask))
        $netTask.Wait(-1) | Out-Null
        $netTask.Result
    }
}
catch {
    Exit-WithError "init_failed" $_.Exception.Message
}

if (-not (Test-Path -LiteralPath $Path)) {
    Exit-WithError "not_found" "image file does not exist"
}

try {
    $bytes = [System.IO.File]::ReadAllBytes($Path)
}
catch {
    Exit-WithError "read_failed" $_.Exception.Message
}

$engine = $null
try {
    $candidates = @($Language, "zh-Hans", "en-US") | Where-Object { -not [string]::IsNullOrWhiteSpace($_) }
    foreach ($tag in $candidates) {
        try {
            $lang = New-Object Windows.Globalization.Language($tag)
            $candidate = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage($lang)
            if ($null -ne $candidate) {
                $engine = $candidate
                break
            }
        }
        catch {
            # This language has no OCR pack; try the next one.
        }
    }
    if ($null -eq $engine) {
        $engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
    }
}
catch {
    Exit-WithError "engine_failed" $_.Exception.Message
}

if ($null -eq $engine) {
    Exit-WithError "no_engine" "no OCR recognizer is available for the current language"
}

try {
    $stream = New-Object System.IO.MemoryStream(, $bytes)
    $ras = [System.IO.WindowsRuntimeStreamExtensions]::AsRandomAccessStream($stream)
    $decoder = Await ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($ras)) ([Windows.Graphics.Imaging.BitmapDecoder])
    $bitmap = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
    $ocr = Await ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
}
catch {
    $inner = $_.Exception
    while ($inner.InnerException) { $inner = $inner.InnerException }
    Exit-WithError "ocr_failed" $inner.Message
}

# Windows OCR inserts a space between every CJK character. Strip whitespace between
# CJK characters/punctuation, but keep spaces inside Latin words.
$lines = New-Object System.Collections.Generic.List[string]
$lineRecords = New-Object System.Collections.Generic.List[object]
foreach ($line in $ocr.Lines) {
    $text = $line.Text
    $text = [regex]::Replace($text, '(?<=[\u4e00-\u9fff\u3000-\u303f\uff00-\uffef])\s+(?=[\u4e00-\u9fff\u3000-\u303f\uff00-\uffef])', '')
    $text = $text.Trim()
    if ($text.Length -gt 0) {
        $lines.Add($text)

        $left = [double]::MaxValue
        $top = [double]::MaxValue
        $right = 0.0
        $bottom = 0.0
        foreach ($word in $line.Words) {
            $rect = $word.BoundingRect
            if ($rect.X -lt $left) { $left = $rect.X }
            if ($rect.Y -lt $top) { $top = $rect.Y }
            if (($rect.X + $rect.Width) -gt $right) { $right = $rect.X + $rect.Width }
            if (($rect.Y + $rect.Height) -gt $bottom) { $bottom = $rect.Y + $rect.Height }
        }
        if ($left -eq [double]::MaxValue) {
            $left = 0
            $top = 0
            $right = 0
            $bottom = 0
        }
        $lineRecords.Add([pscustomobject]@{
            text = $text
            x    = [int]$left
            y    = [int]$top
            w    = [int]($right - $left)
            h    = [int]($bottom - $top)
        })
    }
}

$joined = [string]::Join("`n", $lines)

Write-Result @{
    ok         = $true
    text       = $joined
    lines      = $lineRecords
    language   = $engine.RecognizerLanguage.LanguageTag
    width      = $decoder.PixelWidth
    height     = $decoder.PixelHeight
    line_count = $lines.Count
}
exit 0
