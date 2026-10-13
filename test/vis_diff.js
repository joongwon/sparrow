// Run with node test/vis_diff.js. No browser or npm dependencies required.
const fs = require('fs'), path = require('path'), vm = require('vm');
const assert = require('assert').strict;
const source = fs.readFileSync(path.join(__dirname, '../src/core/visHtml.ml'), 'utf8');
const script = source.match(/let js\s*=\s*\{\|([\s\S]*?)\|}/)[1];
const context = {document: {getElementById: () => null}};
vm.createContext(context); vm.runInContext(script, context);
const diff = (a, b) => JSON.parse(JSON.stringify(context.diffStates(a, b)));
assert.deepEqual(diff('{ x -> 1\ny -> 2 }', '{ x -> 3\nz -> 4 }'), {
  removed: ['x -> 1', 'y -> 2'], added: ['x -> 3', 'z -> 4']
});
assert.deepEqual(diff('{ x -> 1\ny -> 2 }', '{ y -> 2\nx -> 1 }'), {removed: [], added: []});
assert.deepEqual(diff('{ x -> 1\nx -> 1 }', '{ x -> 1 }'), {removed: ['x -> 1'], added: []});
const omit = context.omitTrivialFunctionBindings;
assert.deepEqual(diff(omit('{ f -> ( bot, bot, bot, bot, {f} ) }'),
  omit('{ f -> ( bot, bot, bot, bot, {f} )\ng -> ( bot, bot, bot, bot, {g} ) }')),
  {removed: [], added: []});
assert.deepEqual(diff('bot', '{ x -> 1 }'), {removed: ['bot'], added: ['x -> 1']});
assert.equal(omit('{ x -> 1\nf -> ( bot, bot, bot, bot, {f} )\ny -> 2 }'),
  '1 trivial function binding omitted.\n{ x -> 1\ny -> 2 }');
assert.deepEqual(diff('{ x -> <script>alert(1)</script> }', 'bot'), {
  removed: ['x -> <script>alert(1)</script>'], added: ['bot']
});
console.log('State diff checks passed');
