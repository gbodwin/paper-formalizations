'use strict'
/* SOURCE ONLY, never invoked. Public SDK calls follow actions/download-artifact
 * d3f86a106a0bac45b974a628896c90dbdf5c8093 with its exact lockfile (artifact2.3.2).
 * Unlike that action's warning, any absent/mismatching digest result is fatal.
 * There is no token/findBy/repository/run override and no REST permission grant.
 */
const fs = require('node:fs')
const path = require('node:path')
const crypto = require('node:crypto')
const {execFileSync} = require('node:child_process')
const here = __dirname
const root = path.resolve(here, '../..')
const controls = ['closure_contract.py', 'HeaderProbe.lean', 'targets.json',
  'strict_download.cjs', 'package.json', 'package-lock.json']
const specs = ['light-eft-paid-focused-adapter-20261020',
  'light-eft-joint-flag-ci-extension-revision-20261019',
  'light-eft-canonical-output-adapter-20261020',
  'light-eft-paid-joint-bridge-ci-adapter-20261020',
  'light-eft-fair-bit-batch-ci-adapter-20261021']
function need(ok, message) { if (!ok) throw new Error(message) }
function hash(raw) { return crypto.createHash('sha256').update(raw).digest('hex') }
function git(...args) { return execFileSync('git', args, {cwd: root, timeout: 10000}) }
function digest(value) {
  need(typeof value === 'string', 'Missing artifact digest')
  const result = value.replace(/^sha256:/, '')
  need(/^[0-9a-f]{64}$/.test(result), 'Invalid artifact digest')
  return result
}
function loadedBindings(nodeRoot) {
  const result = {}
  for (const file of Object.keys(require.cache)) {
    const real = fs.realpathSync(file)
    if (real === fs.realpathSync(__filename)) continue
    need(real.startsWith(nodeRoot + path.sep) && !fs.lstatSync(file).isSymbolicLink(),
      'SDK loaded code outside the exact local dependency tree')
    const bytes = fs.readFileSync(real)
    result[path.relative(here, real).split(path.sep).join('/')] = {bytes: bytes.length, sha256: hash(bytes)}
    need(Object.keys(result).length <= 8192, 'SDK loaded-code manifest exceeds bound')
  }
  return result
}
function exactControls() {
  const bound = {}
  for (const name of controls) {
    const file = path.join(here, name)
    const rel = path.relative(root, file).split(path.sep).join('/')
    const bytes = fs.readFileSync(file)
    need(!fs.lstatSync(file).isSymbolicLink() && bytes.equals(git('show', 'HEAD:' + rel)),
      'Source control differs: ' + rel)
    bound[rel] = {path: rel, bytes: bytes.length, sha256: hash(bytes)}
  }
  for (const spec of specs) {
    const rel = `checkpoints/${spec}/ci-spec.json`
    const bytes = fs.readFileSync(path.join(root, rel))
    need(bytes.equals(git('show', 'HEAD:' + rel)), 'Specification differs')
    const rows = new Map(JSON.parse(bytes).engine_files.map(r => [r.path, r]))
    for (const [rel, row] of Object.entries(bound)) {
      const actual = rows.get(rel)
      need(actual && actual.path === row.path && actual.bytes === row.bytes && actual.sha256 === row.sha256,
        'Transport control not bound in every spec: ' + rel)
    }
  }
  return bound
}
async function main() {
  const e = process.env
  need(e.GITHUB_ACTIONS === 'true' && e.GITHUB_REPOSITORY === 'gbodwin/paper-formalizations' &&
    e.GITHUB_WORKFLOW === 'Lean' && e.GITHUB_JOB === 'check' &&
    e.LIGHTEFT_VALIDATION_ROLE === 'global_replay', 'Wrong actual transport job')
  const head = git('rev-parse', 'HEAD').toString().trim()
  need(/^[0-9a-f]{40}$/.test(head) && e.GITHUB_SHA === head && e.LIGHTEFT_EXPECTED_SOURCE === head &&
    e.GITHUB_WORKFLOW_SHA === head && e.LEAN_NUM_THREADS === '1', 'Exact source/worker differs')
  need(e.GITHUB_WORKFLOW_REF === `${e.GITHUB_REPOSITORY}/.github/workflows/lean.yml@${e.GITHUB_REF}` &&
    e.LIGHTEFT_JOB_WORKFLOW_REPOSITORY === e.GITHUB_REPOSITORY &&
    e.LIGHTEFT_JOB_WORKFLOW_PATH === '.github/workflows/light-eft-global-replay.yml' &&
    e.LIGHTEFT_JOB_WORKFLOW_SHA === head &&
    [`${e.GITHUB_REPOSITORY}/.github/workflows/light-eft-global-replay.yml@${e.GITHUB_REF}`,
     `${e.GITHUB_REPOSITORY}/.github/workflows/light-eft-global-replay.yml@${head}`]
      .includes(e.LIGHTEFT_JOB_WORKFLOW_REF), 'Actual reusable workflow differs')
  for (const key of ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'LIGHTEFT_HANDOFF_ARTIFACT_ID'])
    need(/^[1-9][0-9]*$/.test(e[key] || ''), 'Invalid same-run identity: ' + key)
  need(e.LIGHTEFT_HANDOFF_PRODUCER_SHA === head &&
    e.LIGHTEFT_HANDOFF_PRODUCER_RUN_ID === e.GITHUB_RUN_ID &&
    e.LIGHTEFT_HANDOFF_PRODUCER_RUN_ATTEMPT === e.GITHUB_RUN_ATTEMPT,
    'Producer outputs are not this run/attempt/source')
  need(!e.INPUT_GITHUB_TOKEN && !e.INPUT_REPOSITORY && !e.INPUT_RUN_ID,
    'Cross-run/token transport overrides are forbidden')
  const expectedDigest = digest(e.LIGHTEFT_HANDOFF_ARTIFACT_DIGEST)
  need(/^[0-9a-f]{64}$/.test(e.LIGHTEFT_HANDOFF_MANIFEST_SHA256 || ''), 'Missing producer manifest output')
  const id = Number(e.LIGHTEFT_HANDOFF_ARTIFACT_ID)
  need(Number.isSafeInteger(id) && id > 0, 'Artifact ID is not an exact safe integer')
  const name = `light-eft-replay-handoff-${e.GITHUB_RUN_ID}-${e.GITHUB_RUN_ATTEMPT}`
  const sourceControls = exactControls() // Current unmodified five specs refuse here.
  const lock = JSON.parse(fs.readFileSync(path.join(here, 'package-lock.json')))
  need(lock.packages['node_modules/@actions/artifact'].version === '2.3.2' &&
    lock.packages['node_modules/@actions/artifact'].integrity ===
      'sha512-uX2Mr5KEPcwnzqa0Og9wOTEKIae6C/yx9P/m8bIglzCS5nZDkcQC/zRWjjoEsyVecL6oQpBx5BuqQj/yuVm0gw==',
    'Pinned SDK dependency differs')
  const parent = fs.realpathSync(e.RUNNER_TEMP)
  const home = path.join(parent, `light-eft-handoff-${e.GITHUB_RUN_ID}-${e.GITHUB_RUN_ATTEMPT}-${id}`)
  fs.mkdirSync(home, {mode: 0o700}) // No recursive/reuse/replace.
  const destination = path.join(home, 'bundle')
  fs.mkdirSync(destination, {mode: 0o700})
  try {
    // No findBy: the supported SDK uses this job's existing runtime authority.
    need(!e.NODE_PATH && !e.NODE_OPTIONS, 'Inherited Node module/hook override is forbidden')
    const nodeRoot = fs.realpathSync(path.join(here, 'node_modules'))
    need(nodeRoot === path.join(fs.realpathSync(here), 'node_modules') &&
      !fs.lstatSync(path.join(here, 'node_modules')).isSymbolicLink(), 'SDK dependency root is not local')
    const sdkRoot = fs.realpathSync(path.join(nodeRoot, '@actions/artifact'))
    const entry = fs.realpathSync(require.resolve('@actions/artifact'))
    need(sdkRoot === path.join(nodeRoot, '@actions/artifact') && entry.startsWith(sdkRoot + path.sep) &&
      JSON.parse(fs.readFileSync(path.join(sdkRoot, 'package.json'))).version === '2.3.2',
      'Actual resolved SDK entry/version differs')
    const client = require('@actions/artifact').default
    const loadedBefore = loadedBindings(nodeRoot)
    const {artifacts} = await client.listArtifacts({latest: true})
    const matches = artifacts.filter(a => a.id === id)
    need(matches.length === 1, 'Exact artifact is not in the actual current-run listing')
    const actual = matches[0]
    need(actual.name === name && digest(actual.digest) === expectedDigest &&
      Number.isSafeInteger(actual.size) && actual.size > 0, 'Actual artifact metadata differs')
    const outcome = await client.downloadArtifact(id, {path: destination, expectedHash: actual.digest})
    need(outcome.digestMismatch === false, 'Compressed artifact digest was not positively verified')
    if (outcome.downloadPath !== undefined)
      need(fs.realpathSync(outcome.downloadPath) === fs.realpathSync(destination), 'Download destination differs')
    const loadedAfter = loadedBindings(nodeRoot)
    for (const [file, row] of Object.entries(loadedBefore))
      need(loadedAfter[file] && loadedAfter[file].bytes === row.bytes && loadedAfter[file].sha256 === row.sha256,
        'Loaded SDK code changed during transport')
    need(JSON.stringify(exactControls()) === JSON.stringify(sourceControls), 'Transport source controls changed')
    const record = {schema: 'LIGHT_ACTUAL_SDK_TRANSPORT_V1', source_commit: head,
      repository: e.GITHUB_REPOSITORY, run_id: e.GITHUB_RUN_ID, run_attempt: e.GITHUB_RUN_ATTEMPT,
      artifact_id: actual.id, artifact_name: actual.name, artifact_bytes: actual.size,
      artifact_digest: expectedDigest, manifest_sha256: e.LIGHTEFT_HANDOFF_MANIFEST_SHA256,
      current_run_client: true, findBy_used: false, compressed_digest_verified: true,
      digest_mismatch: outcome.digestMismatch, source_controls: sourceControls,
      sdk_version: '2.3.2', sdk_entry: path.relative(here, entry).split(path.sep).join('/'),
      loaded_code: loadedAfter, loaded_code_unchanged: true,
      dependency_qualification: 'Pinned lockfile CI installation; not authenticated build/cache provenance',
      destination: fs.realpathSync(destination)}
    const recordPath = path.join(home, 'transport.json')
    fs.writeFileSync(recordPath, JSON.stringify(record) + '\n', {flag: 'wx', mode: 0o600})
    fs.appendFileSync(e.GITHUB_OUTPUT, `transport_record=${recordPath}\ndownload_directory=${destination}\n`)
  } catch (error) {
    const message = String(error && error.message || error).replace(/https?:\/\/\S+/g, '<redacted-url>')
    fs.writeFileSync(path.join(home, 'transport-failure.json'), JSON.stringify({
      schema: 'LIGHT_ACTUAL_SDK_TRANSPORT_FAILURE_V1', artifact_id: id, source_commit: head,
      run_id: e.GITHUB_RUN_ID, run_attempt: e.GITHUB_RUN_ATTEMPT, error: message,
      partial_data_preserved: true, acceptance: false}) + '\n', {flag: 'wx', mode: 0o600})
    throw new Error(message)
  }
}
main().catch(error => { console.error(String(error.message).replace(/https?:\/\/\S+/g, '<redacted-url>')); process.exitCode = 1 })
