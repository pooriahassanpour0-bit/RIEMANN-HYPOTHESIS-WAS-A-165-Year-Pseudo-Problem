#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
build_zrap_omega2.py
ZRAP Ω² — Dual-Layer Reflective VisionFrame (Offline Single-File Builder)
Produces: ZRAP_VisionFrame_Omega2_full.html
"""

from pathlib import Path
import json
import sys
import itertools

OUT_HTML = "ZRAP_VisionFrame_Omega2_full.html"
PLOTLY_CANDIDATES = [
    "plotly-2.32.2.min.js",
    "plotly-2.32.0.min.js",
    "plotly-2.32.1.min.js",
    "plotly.min.js",
    "plotly.js"
]

# -----------------------
# داده‌های نمونه (از خروجی Colab / Gemini)
#  - x: zero index (1..20)
#  - y: derivative order n (0..6)
#  - z_base: پایه‌ی مقدار log10|Λ| برای هر لایه؛ سپس هر لایه با scale و فاز متفاوت ساخته می‌شود
# -----------------------
x = [[i for i in range(1, 21)] for _ in range(7)]
y = [[n]*20 for n in range(7)]

# z_base: نمونه‌ای از داده واقعی که قبلاً تولید شد (۷x20) - نشان‌دهنده ΛR نزدیک صفر
z_base = [
[-0.6289720835,-0.6289720030,-0.6289719269,-0.6289718385,-0.6289717541,-0.6289716361,-0.6289715332,-0.6289714571,-0.6289712978,-0.6289712393,-0.6289711156,-0.6289709597,-0.6289708250,-0.6289707556,-0.6289705671,-0.6289704516,-0.6289703320,-0.6289701759,-0.6289699990,-0.6289695359998],
[0.3491322514,0.3491323319,0.3491324080,0.3491324965,0.3491325808,0.3491326989,0.3491328017,0.3491328779,0.3491330371,0.3491330957,0.3491332194,0.3491333753,0.3491335099,0.3491335794,0.3491337678,0.3491338833,0.3491340030,0.3491341590,0.3491343360,0.3491341541198764],
[1.6505239482,1.6505240287,1.6505241048,1.6505241933,1.6505242776,1.6505243957,1.6505244985,1.6505245746,1.6505247339,1.6505247925,1.6505249162,1.6505250721,1.6505252068,1.6505252762,1.6505254646,1.6505255801,1.6505256997,1.6505258558,1.6505260327,1.6505261122],
[3.1276454439,3.1276455244,3.1276456005,3.1276456890,3.1276457733,3.1276458914,3.1276459942,3.1276460704,3.1276462296,3.1276462882,3.1276464119,3.1276465678,3.1276467025,3.1276467719,3.1276469603,3.1276470758,3.1276471954,3.1276473515,3.1276475284,3.1276476079],
[4.7297053751,4.7297054556,4.7297055317,4.7297056202,4.7297057045,4.7297058226,4.7297059254,4.7297060016,4.7297061608,4.7297062194,4.7297063431,4.7297064990,4.7297066337,4.7297067031,4.7297068915,4.7297070070,4.7297071267,4.7297072827,4.7297074597,4.7297075391],
[6.4286753794,6.4286754599,6.4286755360,6.4286756244,6.4286757088,6.4286758268,6.4286759297,6.4286760058,6.4286761651,6.4286762236,6.4286763473,6.4286765032,6.4286766379,6.4286767073,6.4286768958,6.4286770113,6.4286771309,6.4286772870,6.4286774639,6.4286775434],
[8.2068266298,8.2068267103,8.2068267864,8.2068268748,8.2068269592,8.2068270772,8.2068271801,8.2068272562,8.2068274155,8.2068274740,8.2068275977,8.2068277536,8.2068278883,8.2068279577,8.2068281462,8.2068282617,8.2068283813,8.2068285374,8.2068287143,8.2068287938]
]

# لیست 100 صفر (Im values) — از خروجی تو
zeros_im = [
14.134725141,21.022039639,25.01085758,30.424876125,32.935061588,37.586178159,40.918719012,43.327073281,48.005150881,49.773832478,
52.970321478,56.446247697,59.347044003,60.831778525,65.112544048,67.079810529,69.546401711,72.067157674,75.704690699,77.144840069,
79.33737502,82.910380854,84.735492981,87.425274613,88.809111208,92.49189927,94.651344041,95.870634228,98.831194218,101.317851006,
103.72553804,105.446623052,107.168611184,111.029535543,113.109428663,114.163699225,116.226680321,118.790782866,121.370125002,122.946829294,
124.256818554,127.51668388,129.578704199,131.08768853,133.497737203,134.756509753,138.116042055,139.736208952,141.123707404,143.111845808,
146.000982486,147.422765343,150.053520421,150.925257612,153.024693811,156.112909294,157.597591818,158.849988171,161.188964138,163.030709687,
165.537069188,167.184439978,169.094515416,169.911976479,173.41153652,174.754191523,176.441434298,178.377407776,179.91648402,182.207078484,
184.874467848,185.598783677,187.228922584,189.416158656,192.02665636,193.079726604,195.26539668,196.87648184,198.015309676,201.264751944,
202.493594514,204.189671803,205.394697202,207.906258888,209.576509716,211.690862595,213.347919469,214.547044783,216.169538508,219.067596349,
220.714918839,221.430705555,224.007000254,224.983324676,227.42144428,229.337413306,231.2501887,233.693404179,235.077446102,236.524229666
]

# -----------------------
# پیدا کردن plotly محلی یا fallback به CDN
# -----------------------
def find_plotly():
    # ... (همان تابع find_plotly) ...
    cwd = Path('.').resolve()
    candidates = [cwd]
    # common android dirs
    base = Path("/storage/emulated/0")
    if base.exists():
        for sub in ["Download", "Downloads", "Pydroid3", "Documents", "مانیفست پارادایم"]:
            p = base / sub
            if p.exists():
                candidates.append(p)
        candidates.append(base)
    # بررسی هر مسیر برای نامزدها
    for folder in candidates:
        for name in PLOTLY_CANDIDATES:
            p = folder / name
            if p.exists() and p.is_file():
                return p
    return None

plotly_path = find_plotly()
use_cdn = False
plotly_js = None
if plotly_path:
    print("Using local Plotly:", plotly_path)
    plotly_js = plotly_path.read_text(encoding='utf-8', errors='replace')
else:
    print("Local Plotly JS not found — fallback to CDN (requires internet).")
    use_cdn = True
    # CDN target (if offline file absent, will use this URL in HTML)
    plotly_cdn = "https://cdn.plot.ly/plotly-2.32.2.min.js"

# -----------------------
# محاسبه حدود z برای contours
# -----------------------
z_flat = list(itertools.chain.from_iterable(z_base))
z_min = min(z_flat)
z_max = max(z_flat)
z_range = z_max - z_min if z_max != z_min else 1.0
contour_step = z_range / 24.0

# JSON encode (ensure_ascii=False keeps Unicode readable)
x_json = json.dumps(x, ensure_ascii=False)
y_json = json.dumps(y, ensure_ascii=False)
z_json = json.dumps(z_base, ensure_ascii=False)
zeros_json = json.dumps(zeros_im, ensure_ascii=False)

# -----------------------
# قالب HTML (ساخت رشتهٔ نهایی)
# -----------------------
head = """<!doctype html>
<html lang="fa">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>ZRAP — VisionFrame Ω² (Dual-Layer)</title>
<style>
:root{--bg:#05040a;--panel:#0a0a10;--accent:#19d3f3;--muted:#9fb8c9;--text:#e6eef6}
html,body{height:100%;margin:0;background:var(--bg);color:var(--text);font-family:Segoe UI,Roboto,Arial,sans-serif}
header{padding:12px;background:linear-gradient(90deg,#071026,#07102b);box-shadow:0 6px 20px rgba(0,0,0,.6)}
h1{margin:0;color:var(--accent);font-size:16px}
.subtitle{color:var(--muted);font-size:12px;margin-top:6px}
#plot{width:100%;height:78vh;background:var(--panel);border-radius:8px;margin-top:10px}
.controls{display:flex;gap:8px;align-items:center;justify-content:center;margin-top:10px;flex-wrap:wrap}
.btn{background:linear-gradient(90deg,#19d3f3,#6ef);border:none;padding:8px 12px;border-radius:6px;color:#012;cursor:pointer;font-weight:600}
.info{color:var(--muted);font-size:12px;text-align:center;margin-top:8px}
footer{color:#7f9aa6;font-size:12px;padding:10px;text-align:center}
</style>
</head>
<body>
<header>
  <h1>ZRAP — Reflective VisionFrame Ω²</h1>
  <div class="subtitle">Dual-layer reflective surfaces (t1=0.1, t2=0.5) — Interactive Offline</div>
</header>

<div style="padding:12px;">
  <div id="plot"></div>
  <div class="controls">
    <button id="playBtn" class="btn">▶ Play</button>
    <button id="pauseBtn" class="btn">⏸ Pause</button>
    <label style="color:var(--muted)">Speed:
      <input id="speed" type="range" min="0.2" max="3.0" step="0.1" value="1.0">
    </label>
    <button id="resetBtn" class="btn">Reset</button>
  </div>
  <div class="info">Dual-layer: blue-green = t1=0.1 (opaque), magenta-yellow = t2=0.5 (semi-transparent). Symmetry plane (Rₐ) shown faintly.</div>
</div>
"""

# embed plotly if local, otherwise include script tag to CDN
if plotly_js:
    plotly_block = "\n<script>\n" + plotly_js + "\n</script>\n"
else:
    plotly_block = f'\n<script src="{plotly_cdn}"></script>\n'

# main JS (use unique placeholders <<...>> to avoid accidental format conflicts)
main_js_template = """
<script>
// embedded JSON data (injected by Python)
var X_DATA = <<X_DATA>>;
var Y_DATA = <<Y_DATA>>;
var Z_BASE = <<Z_BASE>>;
var ZEROS_IM = <<ZEROS_IM>>;

var Z_MIN = <<Z_MIN>>;
var Z_MAX = <<Z_MAX>>;
var CONTOUR_STEP = <<CONTOUR_STEP>>;

// build two layers from Z_BASE with different modulation (t1,t2)
function buildLayer(zbase, framesCount, phaseOffset, scaleBase) {
  var frames = [];
  for (var f=0; f<framesCount; f++) {
    var phase = (f/framesCount) * Math.PI * 2;
    var scale = scaleBase + 0.06 * Math.sin(phase + phaseOffset);
    var zf = [];
    for (var i=0;i<zbase.length;i++){
      var row = [];
      for (var j=0;j<zbase[i].length;j++){
        // small modulation to simulate regulator effect
        var val = zbase[i][j] * scale * (1 + 0.015 * Math.cos(phase*1.2 + i*0.12 + j*0.07));
        row.push(val);
      }
      zf.push(row);
    }
    frames.push({name: "f"+f, data:[{z: zf}]});
  }
  return frames;
}

// build trace objects
var layer1 = {
  x: X_DATA,
  y: Y_DATA,
  z: Z_BASE,
  type: 'surface',
  name: 't=0.1',
  showscale: true,
  opacity: 0.96,
  colorscale: [[0,"#0d0887"],[0.25,"#31688e"],[0.5,"#35b779"],[0.75,"#b5de2b"],[1,"#fde725"]],
  contours: { z: { show:true, start: Z_MIN, end: Z_MAX, size: CONTOUR_STEP } }
};

var layer2 = {
  x: X_DATA,
  y: Y_DATA,
  // z for layer2 will be provided via frames (initially same as base)
  z: Z_BASE,
  type: 'surface',
  name: 't=0.5',
  showscale: false,
  opacity: 0.52,
  colorscale: [[0,"#3a034b"],[0.25,"#6a176e"],[0.5,"#b33086"],[0.75,"#ff7fbf"],[1,"#ffd6f0"]],
  contours: { z: { show:false } }
};

// symmetry plane (R_a guide)
var symPlane = {
  type: 'surface',
  x: [[X_DATA[0][0], X_DATA[0][X_DATA[0].length-1]], [X_DATA[0][0], X_DATA[0][X_DATA[0].length-1]]],
  y: [[Y_DATA[0][0], Y_DATA[0][0]], [Y_DATA[Y_DATA.length-1][0], Y_DATA[Y_DATA.length-1][0]]],
  z: [[Z_MIN-0.3, Z_MIN-0.3],[Z_MAX+0.3, Z_MAX+0.3]],
  showscale: false,
  opacity: 0.08,
  surfacecolor: [['#ffffff','#ffffff'], ['#ffffff','#ffffff']],
  hoverinfo: 'skip'
};

// zero markers (map zeros to grid spots)
var zeroX = [], zeroY = [], zeroZ = [], zeroText = [];
for (var i=0;i<ZEROS_IM.length;i++){
  var xi = i % X_DATA[0].length;
  var yi = Math.floor(i / X_DATA[0].length);
  if (yi >= Z_BASE.length) yi = Z_BASE.length - 1;
  zeroX.push(X_DATA[yi][xi]);
  zeroY.push(Y_DATA[yi][xi]);
  zeroZ.push(Z_BASE[yi][xi] + 0.06);
  zeroText.push("Zero#" + (i+1) + " Im=" + ZEROS_IM[i].toFixed(6));
}

var zeroTrace = {
  x: zeroX, y: zeroY, z: zeroZ,
  mode: 'markers+text',
  type: 'scatter3d',
  marker: { color: 'cyan', size: 4, line: {width:1, color:'#001'} },
  text: zeroText,
  textposition: 'top center',
  hovertemplate: "%{text}<br>log10|Λ|=%{z}<extra></extra>"
};

var layout = {
  title: { text: "ZRAP — Dual Reflective Λᴿ Surfaces: t1=0.1 & t2=0.5", font: {color:'#19d3f3'} },
  paper_bgcolor: '#05040a',
  plot_bgcolor: '#05040a',
  scene: {
    xaxis: { title: "Zero Index (Im(s₀))", titlefont: {color:'#cfe8f2'}, tickfont:{color:'#cfe8f2'} },
    yaxis: { title: "Derivative Order n", titlefont: {color:'#cfe8f2'}, tickfont:{color:'#cfe8f2'} },
    zaxis: { title: "log10 |Λᴿ|", titlefont: {color:'#cfe8f2'}, tickfont:{color:'#cfe8f2'} },
    camera: { eye: { x: 1.6, y: 1.1, z: 0.7 } }
  },
  autosize: true,
  margin: { l:60, r:30, b:40, t:80 }
};

// frames for each layer
var FRAMES1 = buildLayer(Z_BASE, 50, 0.0, 1.00); // layer1 frames
var FRAMES2 = buildLayer(Z_BASE, 50, Math.PI, 1.08); // layer2 frames (phase-shifted)

// merge frames so that both layers animate together (produce array of frames with both z updates)
var FRAMES = [];
for (var k=0; k<FRAMES1.length; k++){
  FRAMES.push({ name: "f"+k, data: [{ z: FRAMES1[k].data[0].z }, { z: FRAMES2[k].data[0].z }] });
}

// initial plot: layer1, layer2, zeroTrace, symPlane
Plotly.newPlot('plot', [layer1, layer2, zeroTrace, symPlane], layout, {responsive:true, displayModeBar:true}).then(function(){
  Plotly.addFrames('plot', FRAMES);
});

// animation control logic
var playing = false; var animHandle = null; var currentFrame = 0; var speed = 1.0;

function playAnim(){
  if (playing) return;
  playing = true;
  function step(){
    if (!playing) return;
    Plotly.animate('plot', [{name:"f" + currentFrame}], {frame:{duration:90/speed, redraw:true}, transition:{duration:60/speed}});
    currentFrame = (currentFrame + 1) % FRAMES.length;
    animHandle = setTimeout(step, 90 / speed);
  }
  step();
}

function pauseAnim(){
  playing = false;
  if (animHandle){ clearTimeout(animHandle); animHandle = null; }
}

document.getElementById('playBtn').addEventListener('click', function(){ playAnim(); });
document.getElementById('pauseBtn').addEventListener('click', function(){ pauseAnim(); });
document.getElementById('resetBtn').addEventListener('click', function(){ pauseAnim(); currentFrame = 0; Plotly.animate('plot',[{name:'f0'}],{frame:{duration:200,redraw:true},transition:{duration:120}}); });
document.getElementById('speed').addEventListener('input', function(e){ speed = parseFloat(e.target.value || 1.0); });

// cleanup on unload
window.addEventListener('beforeunload', function(){ try{ Plotly.purge('plot'); } catch(e){} });
</script>
"""

# -----------------------
# درج مقادیر در قالب (با placeholder replacement امن)
# -----------------------
main_js = main_js_template.replace("<<X_DATA>>", x_json)\
                         .replace("<<Y_DATA>>", y_json)\
                         .replace("<<Z_BASE>>", z_json)\
                         .replace("<<ZEROS_IM>>", zeros_json)\
                         .replace("<<Z_MIN>>", json.dumps(z_min))\
                         .replace("<<Z_MAX>>", json.dumps(z_max))\
                         .replace("<<CONTOUR_STEP>>", json.dumps(contour_step))

# -----------------------
# نوشتن HTML نهایی
# -----------------------
html = head + plotly_block + main_js + "\n</body>\n</html>"

try:
    Path(OUT_HTML).write_text(html, encoding='utf-8')
    # پاسخ نهایی به کاربر:
    print("-------------------------------------------------")
    print("✅ فایل VisionFrame Ω² تولید شد:", Path(OUT_HTML).resolve())
    if plotly_path:
        print("✅ از Plotly محلی استفاده شد:", plotly_path)
    else:
        print("⚠️ Plotly محلی یافت نشد — HTML از CDN استفاده می‌کند (نیاز به اینترنت برای نمایش).")
    print("لطفاً فایل را با مرورگر یا HTML Viewer باز کنید تا دیکوتومی ساختاری متحرک (Dimensional Flatness) را مشاهده کنید.")
    print("-------------------------------------------------")
except Exception as e:
    print(f"❌ خطایی در تولید فایل HTML رخ داد: {e}")
