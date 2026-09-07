// Release-only: run from the isolated candidate after its fresh build/pack.
// node test/release-smoke.mjs /absolute/package.tgz /absolute/new-consumer
// Leaves the consumer and release-evidence.json in place, including on failure.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  copyFileSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  realpathSync,
  writeFileSync,
} from 'node:fs';
import { createRequire } from 'node:module';
import { basename, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const runtimeExports = [
  'Value',
  'and',
  'createSolver',
  'getAllSolutions',
  'getSolution',
  'implies',
  'not',
  'or',
  'xor',
];
const typeExports = [
  'BooleanExpr',
  'SatSolver',
  'SolveOptions',
  'SolverStats',
  'Variable',
  'VariableAssignments',
  'VariablePriority',
];
const modules = ['compile', 'expr', 'index', 'solver'];
const hash = (bytes, algorithm = 'sha256') => createHash(algorithm).update(bytes).digest('hex');
const json = (path) => JSON.parse(readFileSync(path, 'utf8'));
const writeJson = (path, value) => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);
const inside = (root, path) => {
  const rel = relative(root, path);
  return rel !== '..' && !rel.startsWith(`..${sep}`) && !isAbsolute(rel);
};
const fingerprint = (path) => {
  const bytes = readFileSync(path);
  return { path, bytes: bytes.length, sha256: hash(bytes) };
};

const args = process.argv.slice(2);
assert.equal(
  args.length,
  2,
  'Usage: node test/release-smoke.mjs <absolute-tarball-path> <absolute-new-consumer-directory>',
);
assert.ok(args.every(isAbsolute), 'Both paths must be absolute');
const candidate = realpathSync(fileURLToPath(new URL('../', import.meta.url)));
const tarball = realpathSync(args[0]);
assert.ok(lstatSync(tarball).isFile(), 'Tarball must be a regular file');
const requestedConsumer = resolve(args[1]);
const consumer = join(realpathSync(dirname(requestedConsumer)), basename(requestedConsumer));
assert.ok(!inside(candidate, consumer), 'Consumer and evidence must be outside the candidate');
assert.ok(!inside(consumer, candidate), 'Consumer must not contain the candidate');

// Do not resolve TypeScript through cwd or ancestor node_modules fallbacks.
const toolchain = join(candidate, 'node_modules', 'typescript');
const tsApi = realpathSync(join(toolchain, 'lib', 'typescript.js'));
const tsCli = realpathSync(join(toolchain, 'lib', 'tsc.js'));
assert.ok(
  inside(toolchain, tsApi) && inside(toolchain, tsCli),
  'TypeScript must be candidate-local',
);
const ts = createRequire(import.meta.url)(tsApi);

// Non-recursive mkdir also rejects existing directories and dangling symlinks.
// The caller checks the existing external parent with ls before invoking us.
mkdirSync(consumer);
const evidencePath = join(consumer, 'release-evidence.json');
const tarballBytes = readFileSync(tarball);
const integrity = `sha512-${createHash('sha512').update(tarballBytes).digest('base64')}`;
const evidence = {
  schemaVersion: 1,
  status: 'running',
  candidate,
  consumer,
  node: { executable: process.execPath, version: process.version },
  tarball: {
    path: tarball,
    requestedPath: args[0],
    bytes: tarballBytes.length,
    sha256: hash(tarballBytes),
    sha512: hash(tarballBytes, 'sha512'),
    integrity,
  },
  toolchain: { version: ts.version, api: fingerprint(tsApi), cli: fingerprint(tsCli) },
  tooling: ['release-smoke.mjs', 'release-consumer.mjs', 'release-consumer.mts'].map((name) =>
    fingerprint(join(candidate, 'test', name)),
  ),
  commands: [],
};

// Child processes get neither Node loaders/preloads nor inherited npm settings.
// A fresh offline npm cache and empty config files also prevent registry use.
const env = Object.fromEntries(
  Object.entries(process.env).filter(
    ([key]) =>
      !/^(NODE_OPTIONS|NODE_PATH|NODE_V8_COVERAGE|TS_NODE_.*|TSX_.*|NPM_CONFIG_.*)$/i.test(key),
  ),
);
Object.assign(env, {
  NODE_ENV: 'production',
  npm_config_cache: join(consumer, '.npm-cache'),
  npm_config_userconfig: join(consumer, '.npmrc'),
  npm_config_globalconfig: join(consumer, '.npmrc-global'),
});
evidence.environment = {
  nodeOptions: null,
  nodePath: null,
  nodeEnv: env.NODE_ENV,
  npmOffline: true,
  npmIgnoreScripts: true,
  npmCache: env.npm_config_cache,
};

function run(executable, arguments_) {
  const result = spawnSync(executable, arguments_, {
    cwd: consumer,
    env,
    encoding: 'utf8',
    maxBuffer: 8 * 1024 * 1024,
  });
  const record = {
    executable,
    arguments: arguments_,
    cwd: consumer,
    status: result.status,
    signal: result.signal,
    stdout: result.stdout ?? '',
    stderr: result.stderr ?? '',
    error: result.error?.message ?? null,
  };
  evidence.commands.push(record);
  assert.equal(record.error, null, `Unable to execute ${executable}: ${record.error}`);
  assert.equal(result.status, 0, `${executable} failed:\n${record.stderr}\n${record.stdout}`);
  return record.stdout;
}

function inventory(root, subdir = '') {
  const files = [];
  for (const name of readdirSync(join(root, subdir)).sort()) {
    const rel = join(subdir, name);
    const path = join(root, rel);
    const stat = lstatSync(path);
    assert.ok(!stat.isSymbolicLink(), `Installed symlink is forbidden: ${path}`);
    assert.ok(inside(root, realpathSync(path)), `Installed file escaped consumer: ${path}`);
    if (stat.isDirectory()) files.push(...inventory(root, rel));
    else {
      assert.ok(stat.isFile(), `Not a regular installed file: ${path}`);
      files.push(rel);
    }
  }
  return files;
}

function closure(packageRoot, extension) {
  const visited = new Set();
  const edges = [];
  const pending = [`dist/index.${extension}`];
  while (pending.length > 0) {
    const file = pending.pop();
    if (visited.has(file)) continue;
    visited.add(file);
    const path = join(packageRoot, file);
    const info = ts.preProcessFile(readFileSync(path, 'utf8'), true, extension === 'js');
    assert.deepEqual(info.referencedFiles, [], `Unexpected reference paths in ${file}`);
    assert.deepEqual(info.typeReferenceDirectives, [], `Unexpected ambient types in ${file}`);
    assert.deepEqual(info.libReferenceDirectives, [], `Unexpected lib references in ${file}`);
    for (const reference of info.importedFiles) {
      const specifier = reference.fileName;
      assert.match(specifier, /^\.\.?\/.+\.js$/, `Not a relative ESM .js import in ${file}`);
      const target = resolve(
        dirname(path),
        extension === 'd.ts' ? specifier.replace(/\.js$/, '.d.ts') : specifier,
      );
      assert.ok(inside(join(packageRoot, 'dist'), realpathSync(target)), 'Import escaped dist');
      const to = relative(packageRoot, target);
      edges.push({ from: file, specifier, to });
      pending.push(to);
    }
  }
  const files = [...visited].sort();
  assert.deepEqual(files, modules.map((name) => `dist/${name}.${extension}`).sort());
  return { files, edges };
}

function extractReadme(path) {
  const bytes = readFileSync(path);
  const text = bytes.toString('utf8');
  assert.ok(Buffer.from(text).equals(bytes), 'README must be valid UTF-8');
  const lines = text.match(/[^\n]*\n|[^\n]+$/g) ?? [];
  const headings = [];
  const fences = [];
  let open;
  let previousNonempty = '';
  for (const [index, line] of lines.entries()) {
    const content = line.replace(/\r?\n$/, '');
    if (open !== undefined) {
      const closing = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(content);
      if (closing?.[1][0] === open.marker[0] && closing[1].length >= open.marker.length) {
        const code = lines.slice(open.startLine - 1, index).join('');
        fences.push({
          ...open,
          endLine: index,
          code,
          bytes: Buffer.byteLength(code),
          sha256: hash(code),
        });
        open = undefined;
      }
      continue;
    }
    const heading = /^ {0,3}(#{1,6}) (.+)$/.exec(content);
    if (heading !== null) {
      headings.length = heading[1].length - 1;
      headings.push(heading[2]);
    }
    const fence = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(content);
    assert.ok(
      fence !== null || !/`{3,}|~{3,}/.test(content),
      'Unsupported README fence syntax; review it instead of skipping an example',
    );
    if (fence !== null) {
      open = {
        heading: headings.at(-1),
        headingPath: [...headings],
        marker: fence[1],
        language: fence[2].trim(),
        startLine: index + 2,
        precedingText: previousNonempty,
      };
    }
    if (content.trim() !== '') previousNonempty = content;
  }
  assert.equal(open, undefined, 'Unclosed README fence');
  assert.deepEqual(
    fences.map(({ heading, language }) => [heading, language]),
    [
      ['Installation', 'bash'],
      ['Installation', 'bash'],
      ['Basic Usage', 'javascript'],
      ['Finding a Single Solution', 'javascript'],
      ['Finding All Solutions', 'javascript'],
      ['Reusing a Compiled Solver', 'javascript'],
      ['API', 'ts'],
      ['`SolverStats`', 'javascript'],
      ['Ported Hypergraph Heuristic', 'typescript'],
      ['Limits and Development', 'bash'],
    ],
    'README fence inventory changed; review every example, do not silently skip it',
  );
  mkdirSync(join(consumer, 'readme'));
  let runnable = 0;
  return fences.map(({ code, precedingText, ...fence }) => {
    if (fence.language === 'bash') return { ...fence, skipped: 'install/development command' };
    if (fence.language === 'ts') {
      assert.equal(precedingText, 'Type/signature reference (not an executable example):');
      return { ...fence, skipped: 'explicit non-executable API signature reference' };
    }
    runnable += 1;
    const slug = fence.heading
      .toLowerCase()
      .replaceAll('`', '')
      .replace(/[^a-z0-9]+/g, '-');
    const extension = fence.language === 'typescript' ? 'mts' : 'mjs';
    const file = join('readme', `${runnable}-${slug}.${extension}`);
    writeFileSync(join(consumer, file), code, { flag: 'wx' });
    assert.equal(fingerprint(join(consumer, file)).sha256, fence.sha256);
    return { ...fence, file };
  });
}

try {
  writeJson(evidencePath, evidence);
  writeJson(join(consumer, 'package.json'), {
    name: 'sat-release-consumer',
    version: '0.0.0',
    private: true,
    type: 'module',
  });
  writeFileSync(join(consumer, '.npmrc'), '');
  writeFileSync(join(consumer, '.npmrc-global'), '');
  evidence.npmVersion = run('npm', ['--version']).trim();
  run('npm', [
    'install',
    '--offline',
    '--ignore-scripts',
    '--no-audit',
    '--no-fund',
    '--no-update-notifier',
    '--omit=dev',
    '--save-exact',
    '--install-links=true',
    tarball,
  ]);

  const packageRoot = join(consumer, 'node_modules', '@divmain', 'sat');
  assert.equal(realpathSync(packageRoot), packageRoot, 'Package must not be linked');
  const manifest = json(join(packageRoot, 'package.json'));
  assert.equal(manifest.name, '@divmain/sat');
  assert.equal(manifest.version, '2.0.0');
  assert.equal(manifest.type, 'module');
  assert.equal(manifest.main, 'dist/index.js');
  assert.deepEqual(manifest.dependencies, {});
  assert.deepEqual(manifest.files, ['dist']);
  assert.equal(Object.hasOwn(manifest, 'engines'), false);
  for (const field of ['optionalDependencies', 'peerDependencies']) {
    assert.deepEqual(manifest[field] ?? {}, {}, `Unexpected ${field}`);
  }
  for (const field of ['bundleDependencies', 'bundledDependencies']) {
    assert.deepEqual(manifest[field] ?? [], [], `Unexpected ${field}`);
  }
  const installed = json(join(consumer, 'package.json'));
  assert.equal(installed.type, 'module');
  assert.deepEqual(Object.keys(installed.dependencies), ['@divmain/sat']);
  assert.deepEqual(installed.devDependencies ?? {}, {});
  const lock = json(join(consumer, 'package-lock.json'));
  assert.deepEqual(Object.keys(lock.packages).sort(), ['', 'node_modules/@divmain/sat']);
  assert.equal(lock.packages['node_modules/@divmain/sat'].integrity, integrity);
  assert.notEqual(lock.packages['node_modules/@divmain/sat'].link, true);
  const dependencyTree = JSON.parse(run('npm', ['ls', '--all', '--json', '--offline']));
  assert.deepEqual(Object.keys(dependencyTree.dependencies), ['@divmain/sat']);
  assert.deepEqual(dependencyTree.dependencies['@divmain/sat'].dependencies ?? {}, {});
  const nodeModulesFiles = inventory(join(consumer, 'node_modules'));
  assert.ok(
    nodeModulesFiles.every(
      (file) => file === '.package-lock.json' || file.startsWith(`@divmain${sep}sat${sep}`),
    ),
    'Consumer node_modules must contain only @divmain/sat and npm lock metadata',
  );
  const packageFiles = inventory(packageRoot);
  assert.deepEqual(
    packageFiles.filter((file) => file.startsWith(`dist${sep}`)).sort(),
    modules.flatMap((name) => [`dist/${name}.d.ts`, `dist/${name}.js`]).sort(),
  );
  assert.ok(
    packageFiles.every(
      (file) =>
        file.startsWith(`dist${sep}`) ||
        /^(package\.json|README\.md|LICEN[SC]E(?:\.\w+)?)$/i.test(file),
    ),
    'Unexpected files outside dist/package metadata',
  );
  evidence.package = {
    root: packageRoot,
    manifest,
    dependencyTree,
    files: packageFiles.map((file) => ({ ...fingerprint(join(packageRoot, file)), file })),
    javascriptClosure: closure(packageRoot, 'js'),
    declarationClosure: closure(packageRoot, 'd.ts'),
  };

  for (const name of ['release-consumer.mjs', 'release-consumer.mts']) {
    const source = join(candidate, 'test', name);
    const destination = join(consumer, name);
    copyFileSync(source, destination);
    assert.equal(fingerprint(destination).sha256, fingerprint(source).sha256);
  }
  const readme = join(packageRoot, 'README.md');
  evidence.readme = {
    ...fingerprint(readme),
    captureMethod:
      'Exact fence bytes in separate files; a plain-Node wrapper records console.log arguments, then validates them before JSON serialization.',
    fences: extractReadme(readme),
  };
  const snippets = evidence.readme.fences.filter((fence) => fence.file !== undefined);
  assert.equal(snippets.length, 6);
  const configPath = join(consumer, 'tsconfig.json');
  const config = {
    compilerOptions: {
      target: 'ES2022',
      module: 'NodeNext',
      moduleResolution: 'NodeNext',
      lib: ['ES2022', 'DOM'],
      types: [],
      strict: true,
      exactOptionalPropertyTypes: true,
      noUnusedLocals: true,
      noUnusedParameters: true,
      verbatimModuleSyntax: true,
      skipLibCheck: false,
      noEmitOnError: true,
      forceConsistentCasingInFileNames: true,
      rootDir: '.',
      outDir: './emitted',
    },
    files: [
      'release-consumer.mts',
      ...snippets.filter((s) => s.language === 'typescript').map((s) => s.file),
    ],
  };
  writeJson(configPath, config);
  run(process.execPath, [tsCli, '--project', configPath, '--pretty', 'false']);
  const parsed = ts.parseJsonConfigFileContent(config, ts.sys, consumer);
  assert.deepEqual(parsed.errors, []);
  const program = ts.createProgram(parsed.fileNames, parsed.options);
  const diagnostics = ts.getPreEmitDiagnostics(program);
  assert.equal(
    diagnostics.length,
    0,
    ts.formatDiagnosticsWithColorAndContext(diagnostics, {
      getCurrentDirectory: () => consumer,
      getCanonicalFileName: (name) => name,
      getNewLine: () => '\n',
    }),
  );
  const declarationPath = ts.resolveModuleName(
    '@divmain/sat',
    join(consumer, 'release-consumer.mts'),
    parsed.options,
    ts.sys,
  ).resolvedModule?.resolvedFileName;
  assert.equal(declarationPath, join(packageRoot, 'dist', 'index.d.ts'));
  assert.equal(realpathSync(declarationPath), declarationPath);
  const checker = program.getTypeChecker();
  const root = program.getSourceFile(declarationPath);
  assert.ok(root);
  const rootSymbol = checker.getSymbolAtLocation(root);
  assert.ok(rootSymbol);
  const exports = checker.getExportsOfModule(rootSymbol).map((symbol) => {
    const target = symbol.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
    return {
      name: symbol.name,
      value: Boolean(target.flags & ts.SymbolFlags.Value),
      type: Boolean(target.flags & ts.SymbolFlags.Type),
    };
  });
  const values = exports
    .filter((item) => item.value)
    .map((item) => item.name)
    .sort();
  const types = exports
    .filter((item) => item.type && !item.value)
    .map((item) => item.name)
    .sort();
  assert.deepEqual(values, runtimeExports);
  assert.deepEqual(types, typeExports);
  const valueAndTypeExports = exports
    .filter((item) => item.value && item.type)
    .map((item) => item.name)
    .sort();
  assert.deepEqual(valueAndTypeExports, ['Value'], 'Only the enum occupies both namespaces');
  assert.deepEqual(
    exports.map((item) => item.name).sort(),
    [...runtimeExports, ...typeExports].sort(),
  );
  const sources = program.getSourceFiles().map((file) => realpathSync(file.fileName));
  assert.ok(
    sources.every((file) => inside(consumer, file) || inside(join(toolchain, 'lib'), file)),
    'TypeScript consumed sources/ambient declarations outside consumer and candidate TS libs',
  );
  assert.deepEqual(
    sources.filter((file) => inside(packageRoot, file)).sort(),
    modules.map((name) => join(packageRoot, 'dist', `${name}.d.ts`)).sort(),
  );
  const negativeChecks = readFileSync(join(consumer, 'release-consumer.mts'), 'utf8')
    .split('\n')
    .flatMap((line, index) =>
      line.includes('@ts-expect-error') ? [{ line: index + 1, expectation: line.trim() }] : [],
    );
  assert.ok(negativeChecks.length > 0);
  evidence.typescript = {
    config,
    resolution: declarationPath,
    valueExports: values,
    typeOnlyExports: types,
    valueAndTypeExports,
    sources,
    negativeChecks,
    diagnostics: [],
  };

  const probe = join(consumer, 'release-consumer.mjs');
  evidence.runtime = JSON.parse(run(process.execPath, [probe, 'runtime']));
  assert.equal(evidence.runtime.status, 'passed');
  assert.deepEqual(evidence.runtime.exports, runtimeExports);
  assert.equal(evidence.runtime.resolution.realpath, join(packageRoot, 'dist', 'index.js'));
  evidence.typedRuntime = JSON.parse(
    run(process.execPath, [join(consumer, 'emitted', 'release-consumer.mjs')]),
  );
  assert.equal(evidence.typedRuntime.status, 'passed');
  assert.deepEqual(evidence.typedRuntime.types, typeExports);
  for (const snippet of snippets) {
    const executed =
      snippet.language === 'typescript'
        ? join(consumer, 'emitted', snippet.file.replace(/\.mts$/, '.mjs'))
        : join(consumer, snippet.file);
    snippet.executed = fingerprint(executed);
    snippet.result = JSON.parse(
      run(process.execPath, [probe, 'readme', executed, snippet.heading]),
    );
    assert.equal(snippet.result.status, 'passed');
    assert.equal(fingerprint(join(consumer, snippet.file)).sha256, snippet.sha256);
    assert.equal(fingerprint(executed).sha256, snippet.executed.sha256);
  }
  assert.equal(fingerprint(readme).sha256, evidence.readme.sha256);
  assert.equal(fingerprint(tarball).sha256, evidence.tarball.sha256);
  for (const file of evidence.package.files)
    assert.equal(fingerprint(file.path).sha256, file.sha256);
  evidence.consumerFiles = [
    'package.json',
    'package-lock.json',
    'tsconfig.json',
    ...inventory(join(consumer, 'emitted')).map((file) => join('emitted', file)),
  ].map((file) => fingerprint(join(consumer, file)));
  evidence.status = 'passed';
} catch (error) {
  evidence.status = 'failed';
  evidence.failure = { message: String(error), stack: error instanceof Error ? error.stack : null };
  process.exitCode = 1;
} finally {
  writeJson(evidencePath, evidence);
  console.log(JSON.stringify({ status: evidence.status, evidence: evidencePath }, null, 2));
}
