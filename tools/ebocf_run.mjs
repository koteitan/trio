// Evaluate BMS matrices with the matrix -> Extended Buchholz algorithm of Ytosk (Googology Wiki,
// "Algorithm that changes BMS matrices into ordinals up to SRO"), as implemented in
// https://github.com/hemisemidemipresent/bms (src/lib). Set EBOCF_LIB to that src/lib directory.
// stdin: JSON lines {row, M, T}; stdout: JSON lines {row, ok, js, lab, err}, where js = sf(o(M)),
// lab = sf(T), and ok = (js == lab).
import * as readline from "node:readline";
const lib = process.env.EBOCF_LIB;
const { BMSMatrixAnalysis } = await import(lib + "/BMSMatrixAnalysis.js");
const { sf, eq } = await import(lib + "/BMSUtil.js");
function str(a) {
  if (a.length == 0) return "0";
  const t = [];
  while (a.length) {
    t.push(a[0].length == 0 && a[1].length == 0 ? "1"
      : "p" + (a[0].length ? "_{" + str(a[0]) + "}" : "") + "(" + str(a[1]) + ")");
    a = a[2];
  }
  return t.join("+");
}
const rl = readline.createInterface({ input: process.stdin });
for await (const line of rl) {
  const { row, M, T } = JSON.parse(line);
  let js = null, lab = null, err = null;
  try { js = new BMSMatrixAnalysis(M).finalOrdinal(true); } catch (e) { err = "js:" + e.message; }
  try { lab = sf(T); } catch (e) { err = (err || "") + " lab:" + e.message; }
  console.log(JSON.stringify({ row, ok: !!(js && lab && eq(js, lab)),
                               js: js ? str(js) : null, lab: lab ? str(lab) : null, err }));
}
