#!/usr/bin/env python3
import argparse, json, html
from pathlib import Path

def parse_args():
    ap = argparse.ArgumentParser()
    ap.add_argument("trace_json", help="trace.json produced by lean_trace_goals.py")
    ap.add_argument("--out", default="trace.html", help="output html file")
    return ap.parse_args()

def main():
    args = parse_args()
    trace = json.loads(Path(args.trace_json).read_text(encoding="utf-8"))

    lean_file = Path(trace["file"])
    src_text = lean_file.read_text(encoding="utf-8")
    lines = src_text.splitlines()

    # occurrences indexed by line
    by_line = {}
    for occ in trace["occurrences"]:
        by_line.setdefault(occ["line"], []).append(occ)
    for ln in by_line:
        by_line[ln].sort(key=lambda o: (o["col_start"], o["col_end"]))

    # IMPORTANT: do NOT html-escape JSON; just make it safe for </script>
    data_json = json.dumps(trace, ensure_ascii=False)
    data_json = data_json.replace("<", "\\u003c")

    # Build code HTML with per-occurrence spans
    code_rows = []
    for ln, line in enumerate(lines):
        occs = by_line.get(ln, [])
        if not occs:
            code_rows.append(
                f'<div class="row"><span class="ln">{ln+1:4d}</span>'
                f'<span class="code">{html.escape(line)}</span></div>'
            )
            continue

        parts = []
        cur = 0
        for occ in occs:
            a, b = occ["col_start"], occ["col_end"]
            a = max(0, min(len(line), a))
            b = max(0, min(len(line), b))
            if a > cur:
                parts.append(html.escape(line[cur:a]))

            h = occ["hash"]
            seg_text = html.escape(line[a:b])
            parts.append(
                f'<span class="hit" data-h="{h}" data-ln="{ln}" data-a="{a}" data-b="{b}">{seg_text}</span>'
            )
            cur = b

        if cur < len(line):
            parts.append(html.escape(line[cur:]))

        rendered = "".join(parts)
        code_rows.append(
            f'<div class="row"><span class="ln">{ln+1:4d}</span>'
            f'<span class="code">{rendered}</span></div>'
        )

    html_out = f"""<!doctype html>
<html>
<head>
<meta charset="utf-8" />
<title>Lean goal trace: {html.escape(str(lean_file))}</title>
<style>
  body {{
    margin: 0; padding: 0;
    font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial;
    display: grid;
    grid-template-columns: 1.4fr 1fr;
    height: 100vh;
  }}
  #left {{
    border-right: 1px solid #ddd;
    overflow: auto;
    padding: 12px;
  }}
  #right {{
    overflow: auto;
    padding: 12px;
  }}
  .row {{
    white-space: pre;
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
    font-size: 13px;
    line-height: 1.5;
  }}
  .ln {{
    color: #888;
    display: inline-block;
    width: 4.5em;
    user-select: none;
  }}
  .hit {{
    border-radius: 6px;
    padding: 0 2px;
    cursor: pointer;
    background: rgba(255, 230, 150, 0.55);
  }}
  .hit.active {{
    outline: 2px solid rgba(0, 0, 0, 0.35);
    background: rgba(255, 200, 80, 0.75);
  }}
  #goal {{
    white-space: pre-wrap;
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
    font-size: 13px;
    line-height: 1.4;
  }}
  .meta {{
    color: #666;
    font-size: 12px;
    margin-bottom: 10px;
  }}
</style>
</head>
<body>
  <div id="left">
    <div class="meta">
      <div><b>File:</b> {html.escape(str(lean_file))}</div>
      <div><b>Unique states:</b> {len(trace["unique_states"])} &nbsp; <b>Occurrences:</b> {len(trace["occurrences"])}</div>
      <div>Click a highlighted segment to view the cached goal state.</div>
    </div>
    <div id="code">
      {''.join(code_rows)}
    </div>
  </div>
  <div id="right">
    <div class="meta"><b>Goal state</b></div>
    <div id="where" class="meta">No selection.</div>
    <div id="goal">(click a highlighted segment)</div>
  </div>

<script id="trace-data" type="application/json">{data_json}</script>
<script>
  let trace;
  try {{
    trace = JSON.parse(document.getElementById("trace-data").textContent);
  }} catch (e) {{
    console.error("Failed to parse embedded trace-data JSON:", e);
    document.getElementById("goal").textContent = "Error: could not parse trace-data JSON. Check console.";
    throw e;
  }}

  const unique = trace.unique_states;
  let active = null;

  function setActive(el) {{
    if (active) active.classList.remove("active");
    active = el;
    if (active) active.classList.add("active");
  }}

  function renderGoal(hash, ln, a, b) {{
    const goalText = unique[hash] ?? "(missing)";
    document.getElementById("goal").textContent = goalText;
    document.getElementById("where").textContent = `hash=${{hash}}  line=${{ln+1}}  cols=[${{a}},${{b}})`;
  }}

  document.querySelectorAll(".hit").forEach(el => {{
    el.addEventListener("click", () => {{
      setActive(el);
      renderGoal(el.dataset.h, parseInt(el.dataset.ln), parseInt(el.dataset.a), parseInt(el.dataset.b));
    }});
  }});
</script>
</body>
</html>
"""
    Path(args.out).write_text(html_out, encoding="utf-8")
    print(f"wrote {args.out}")

if __name__ == "__main__":
    main()
