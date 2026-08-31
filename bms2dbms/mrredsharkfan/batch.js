// 1 行 1 行列（"(0,0,0)(1,1,1)" 形式）を読んで bmsToDbms の像を同じ形式で書く。
//   node batch.js in.txt out.txt
// core.js は extract.sh で作る。
global.window = {};
require('./core.js');
const f = global.window.bmsToDbms;
const fs = require('fs');
const show = m => m.map(c => '(' + c.join(',') + ')').join('');
const P = s => s.slice(1, -1).split(')(').map(t => t.split(',').map(Number));
const out = [];
for (const s of fs.readFileSync(process.argv[2], 'utf8').split('\n').filter(x => x)) {
  try { out.push(show(f(P(s), 1000000))); }
  catch (e) { out.push('ERR:' + e.message.slice(0, 60)); }
}
fs.writeFileSync(process.argv[3], out.join('\n') + '\n');
