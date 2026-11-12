/**
 * Cookie 管控台 for Surge
 * 版本 1.0.0
 *
 * 同一个脚本承担四种角色，按 Surge 传入的环境自动区分：
 *   1. 管理页面：拦截 http://cookie.ctl 的请求，返回 WebUI 和 JSON 接口
 *   2. 请求改写：按规则修改请求里的 Cookie 头
 *   3. 响应改写：按规则修改响应里的 Set-Cookie 头
 *   4. 定时任务：按设定的间隔重新下载域名列表
 *
 * 数据全部保存在 $persistentStore 中：
 *   CookieCtl.config   用户配置
 *   CookieCtl.index    运行时使用的域名索引（由配置和列表缓存生成）
 *   CookieCtl.meta     各列表的下载状态
 *   CookieCtl.seen     规则模块最近一次运行时的版本号
 *   CookieCtl.src.*    各域名列表的解析结果缓存
 */
'use strict';

var VERSION = '1.0.0';
var UI_HOST = 'cookie.ctl';
var DEFAULT_SCRIPT = 'CookieCtl.js';

var KEY = {
  cfg: 'CookieCtl.config',
  idx: 'CookieCtl.index',
  meta: 'CookieCtl.meta',
  seen: 'CookieCtl.seen',
  src: 'CookieCtl.src.'
};

var LIMIT = {
  rules: 50,
  sources: 20,
  params: 30,
  nameLen: 40,
  valueLen: 512,
  urlLen: 2048,
  extraLen: 50000,
  maxLifeSec: 400 * 86400,
  fetchTimeout: 15,
  fetchConcurrency: 4
};

var UNITS = { s: 1, m: 60, h: 3600, d: 86400 };
var WHERE = ['resp', 'block', 'req', 'reqdel'];
var LIFE_NAMES = { expires: 1, expire: 1, 'max-age': 1, maxage: 1, expiry: 1, lifetime: 1 };
var FLAG_ATTRS = { secure: 'Secure', httponly: 'HttpOnly', partitioned: 'Partitioned' };
var KNOWN_ATTRS = { path: 'Path', domain: 'Domain', samesite: 'SameSite', priority: 'Priority' };
var FALSY_RE = /^(false|0|off|no|关|否|关闭|删除|去掉|remove)$/i;
var TOKEN_RE = /^[!#$%&'*+\-.^_`|~0-9A-Za-z]+$/;
var GLOB_RE = /^[!#$%&'*+\-.^_`|~0-9A-Za-z?]+$/;
var DOMAIN_RE = /^(?=.{1,253}$)[a-z0-9_-]{1,63}(?:\.[a-z0-9_-]{1,63})+$/;
var HOST_CH = '[^\\/:?]';

/* ------------------------------------------------------------------ */
/* 基础工具                                                            */
/* ------------------------------------------------------------------ */

var finished = false;
function finish(result) {
  if (finished) return;
  finished = true;
  try { $done(result || {}); } catch (e) { /* 忽略 */ }
}

function log() {
  try { console.log('[CookieCtl] ' + Array.prototype.join.call(arguments, ' ')); } catch (e) { /* 忽略 */ }
}

function now() { return Date.now(); }

function own(obj, k) { return obj != null && Object.prototype.hasOwnProperty.call(obj, k); }

function sRead(key) {
  try {
    var v = $persistentStore.read(key);
    return typeof v === 'string' ? v : null;
  } catch (e) { return null; }
}

function sWrite(key, val) {
  try { return $persistentStore.write(val, key) !== false; } catch (e) { return false; }
}

function jRead(key, fallback) {
  var s = sRead(key);
  if (!s) return fallback;
  try {
    var v = JSON.parse(s);
    return v == null ? fallback : v;
  } catch (e) { return fallback; }
}

function jWrite(key, obj) { return sWrite(key, JSON.stringify(obj)); }

function hash(str) {
  var h = 0x811c9dc5;
  for (var i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  return h.toString(36);
}

function clampInt(v, lo, hi, def) {
  var n = parseInt(v, 10);
  if (!isFinite(n)) return def;
  return Math.min(hi, Math.max(lo, n));
}

function oneLine(v, max) {
  return String(v == null ? '' : v).replace(/[\x00-\x1f\x7f]+/g, ' ').trim().slice(0, max);
}

function multiLine(v, max) {
  return String(v == null ? '' : v).replace(/\r\n?/g, '\n').replace(/[\x00-\x08\x0b-\x1f\x7f]/g, '').slice(0, max);
}

function newId() {
  return 'r' + Date.now().toString(36) + Math.floor(Math.random() * 1679616).toString(36);
}

function hostOf(url) {
  var m = /^[a-z][a-z0-9+.-]*:\/\/(?:[^@\/?#]*@)?(\[[^\]]*\]|[^:\/?#]+)/i.exec(String(url || ''));
  if (!m) return '';
  return m[1].toLowerCase().replace(/\.+$/, '');
}

function pathOf(url) {
  var m = /^[a-z][a-z0-9+.-]*:\/\/[^\/?#]*(\/[^?#]*)?/i.exec(String(url || ''));
  return (m && m[1]) || '/';
}

function escRe(s) { return String(s).replace(/[.\\+*?^$|()[\]{}\/]/g, '\\$&'); }

var reCache = {};
function getRe(src) {
  if (!src) return null;
  if (own(reCache, src)) return reCache[src];
  var re = null;
  try { re = new RegExp(src, 'i'); } catch (e) { re = null; }
  reCache[src] = re;
  return re;
}

function globListToRe(list) {
  var parts = String(list || '').split(/[\s,，]+/).filter(Boolean).map(function (g) {
    return g.split('').map(function (ch) {
      if (ch === '*') return '.*';
      if (ch === '?') return '.';
      return escRe(ch);
    }).join('');
  });
  return parts.length ? '^(?:' + parts.join('|') + ')$' : '';
}

function isGlobList(s) {
  var parts = String(s || '').split(/[\s,，]+/).filter(Boolean);
  return parts.length > 0 && parts.length <= 20 && parts.every(function (x) { return GLOB_RE.test(x); });
}

function hostGlobRe(glob) {
  return getRe('^' + glob.split('').map(function (ch) {
    if (ch === '*') return '.*';
    if (ch === '?') return '.';
    return escRe(ch);
  }).join('') + '$');
}

function validScriptPath(p) { return /^[^\s,"']{1,512}$/.test(p); }

function utf8Decode(bytes) {
  if (typeof TextDecoder !== 'undefined') return new TextDecoder('utf-8').decode(bytes);
  var out = '';
  for (var i = 0; i < bytes.length; i += 8192) {
    out += String.fromCharCode.apply(null, Array.prototype.slice.call(bytes, i, i + 8192));
  }
  return decodeURIComponent(escape(out));
}

/* ------------------------------------------------------------------ */
/* 请求头 / 响应头                                                       */
/* 兼容两种形式：普通对象，或 full-header-mode 下的 [{field, value}] 数组   */
/* ------------------------------------------------------------------ */

function HeaderBag(raw) {
  var self = this;
  this.isArray = Array.isArray(raw);
  this.items = [];
  this.arrayValued = {};
  if (this.isArray) {
    raw.forEach(function (x) {
      if (x && x.field != null) self.items.push({ f: String(x.field), v: x.value == null ? '' : String(x.value) });
    });
  } else if (raw && typeof raw === 'object') {
    Object.keys(raw).forEach(function (k) {
      var v = raw[k];
      if (Array.isArray(v)) {
        self.arrayValued[k.toLowerCase()] = true;
        v.forEach(function (x) { self.items.push({ f: k, v: String(x) }); });
      } else if (v != null) {
        self.items.push({ f: k, v: String(v) });
      }
    });
  }
}

HeaderBag.prototype.values = function (name) {
  var lname = name.toLowerCase();
  return this.items.filter(function (i) { return i.f.toLowerCase() === lname; }).map(function (i) { return i.v; });
};

HeaderBag.prototype.replace = function (name, values, fallbackField) {
  var lname = name.toLowerCase();
  var pos = -1;
  var field = fallbackField || name;
  var kept = [];
  this.items.forEach(function (it) {
    if (it.f.toLowerCase() === lname) {
      if (pos < 0) { pos = kept.length; field = it.f; }
    } else {
      kept.push(it);
    }
  });
  if (pos < 0) pos = kept.length;
  var add = values.map(function (v) { return { f: field, v: v }; });
  Array.prototype.splice.apply(kept, [pos, 0].concat(add));
  this.items = kept;
};

HeaderBag.prototype.output = function () {
  if (this.isArray) return this.items.map(function (i) { return { field: i.f, value: i.v }; });
  var out = {};
  var first = {};
  var self = this;
  this.items.forEach(function (it) {
    var lk = it.f.toLowerCase();
    if (!own(first, lk)) {
      first[lk] = it.f;
      out[it.f] = self.arrayValued[lk] ? [it.v] : it.v;
      return;
    }
    var f = first[lk];
    if (Array.isArray(out[f])) out[f].push(it.v);
    else out[f] = out[f] + (lk === 'cookie' ? '; ' : ', ') + it.v;
  });
  return out;
};

/* ------------------------------------------------------------------ */
/* 配置                                                                */
/* ------------------------------------------------------------------ */

function defaultConfig() {
  return {
    v: 1,
    enabled: true,
    interval: 24,
    policy: '',
    mitmExclude: '',
    notify: true,
    debug: false,
    scriptPath: '',
    rules: [{
      id: 'baidu',
      name: '百度',
      enabled: true,
      sources: ['https://raw.githubusercontent.com/blackmatrix7/ios_rule_script/master/rule/Surge/Baidu/Baidu.list'],
      extra: '',
      params: [{ where: 'resp', name: 'expires', value: '20', unit: 'd', mode: 'force', only: '' }]
    }]
  };
}

function fixSourceURL(u) {
  var m = /^https?:\/\/github\.com\/([^\/]+)\/([^\/]+)\/blob\/(.+)$/i.exec(u);
  if (m) return 'https://raw.githubusercontent.com/' + m[1] + '/' + m[2] + '/' + m[3];
  return u;
}

function normalizeParam(p, tag, warn) {
  if (!p || typeof p !== 'object') return null;
  var where = WHERE.indexOf(p.where) >= 0 ? p.where : 'resp';
  var name = oneLine(p.name, 64);
  var value = oneLine(p.value, LIMIT.valueLen).replace(/;/g, '');
  var unit = own(UNITS, p.unit) ? p.unit : 'd';
  var mode = p.mode === 'cap' ? 'cap' : 'force';
  var only = oneLine(p.only, 256);

  if (!name) { warn.push(tag + '有一个参数没有填写名称，已忽略'); return null; }

  if (where === 'block' || where === 'reqdel') {
    if (!isGlobList(name)) { warn.push(tag + '的 Cookie 名称「' + name + '」包含不允许的字符，已忽略'); return null; }
    return { where: where, name: name, value: '', unit: unit, mode: mode, only: '' };
  }

  if (!TOKEN_RE.test(name)) { warn.push(tag + '的参数名「' + name + '」包含不允许的字符，已忽略'); return null; }

  if (where === 'resp' && own(LIFE_NAMES, name.toLowerCase())) {
    var n = Number(value);
    if (value === '' || !isFinite(n) || n < 0) {
      warn.push(tag + '的有效期「' + value + '」不是有效的数字，已忽略');
      return null;
    }
    if (n * UNITS[unit] > LIMIT.maxLifeSec) {
      warn.push(tag + '的有效期超过 400 天，已按浏览器上限 400 天保存');
      value = String(Math.floor(LIMIT.maxLifeSec / UNITS[unit]));
    }
  }

  if (where === 'req') only = '';
  if (only && !isGlobList(only)) {
    warn.push(tag + '的「仅作用于」格式不正确，已改为作用于全部 Cookie');
    only = '';
  }
  return { where: where, name: name, value: value, unit: unit, mode: mode, only: only };
}

function normalizeConfig(raw, warn) {
  warn = warn || [];
  if (!raw || typeof raw !== 'object') raw = {};
  var c = {
    v: 1,
    enabled: raw.enabled !== false,
    interval: clampInt(raw.interval, 1, 168, 24),
    policy: oneLine(raw.policy, 64),
    mitmExclude: multiLine(raw.mitmExclude, 4000),
    notify: raw.notify !== false,
    debug: raw.debug === true,
    scriptPath: '',
    rules: []
  };

  var sp = oneLine(raw.scriptPath, 512);
  if (sp) {
    if (validScriptPath(sp)) c.scriptPath = sp;
    else warn.push('脚本路径不能包含空格、逗号或引号，已改回自动');
  }

  var rules = Array.isArray(raw.rules) ? raw.rules : [];
  if (rules.length > LIMIT.rules) warn.push('规则集最多 ' + LIMIT.rules + ' 个，多出的已忽略');
  var ids = {};

  rules.slice(0, LIMIT.rules).forEach(function (r, i) {
    if (!r || typeof r !== 'object') return;
    var id = typeof r.id === 'string' && /^[a-z0-9]{1,24}$/.test(r.id) ? r.id : newId();
    while (own(ids, id)) id = newId();
    ids[id] = 1;

    var name = oneLine(r.name, LIMIT.nameLen) || ('规则集 ' + (i + 1));
    var tag = '「' + name + '」';

    var list = Array.isArray(r.sources) ? r.sources : String(r.sources || '').split(/[\r\n]+/);
    var sources = [];
    list.forEach(function (u) {
      u = oneLine(u, LIMIT.urlLen);
      if (!u) return;
      var fixed = fixSourceURL(u);
      if (fixed !== u) {
        warn.push(tag + '中的 GitHub 页面地址已自动换成 raw 地址');
        u = fixed;
      }
      if (!/^https?:\/\/[^\s\/?#]+\.[^\s\/?#]+(?:[\/?#]\S*)?$/i.test(u)) {
        warn.push(tag + '中有一个地址无效，已忽略：' + u.slice(0, 80));
        return;
      }
      if (sources.indexOf(u) >= 0) return;
      if (sources.length >= LIMIT.sources) {
        warn.push(tag + '最多 ' + LIMIT.sources + ' 个列表地址，多出的已忽略');
        return;
      }
      sources.push(u);
    });

    var params = [];
    var rawParams = Array.isArray(r.params) ? r.params : [];
    if (rawParams.length > LIMIT.params) warn.push(tag + '最多 ' + LIMIT.params + ' 个参数，多出的已忽略');
    rawParams.slice(0, LIMIT.params).forEach(function (p) {
      var np = normalizeParam(p, tag, warn);
      if (np) params.push(np);
    });

    c.rules.push({
      id: id,
      name: name,
      enabled: r.enabled !== false,
      sources: sources,
      extra: multiLine(r.extra, LIMIT.extraLen),
      params: params
    });
  });
  return c;
}

function loadConfig() {
  var raw = jRead(KEY.cfg, null);
  if (!raw || typeof raw !== 'object') {
    var d = defaultConfig();
    jWrite(KEY.cfg, d);
    return d;
  }
  return normalizeConfig(raw, []);
}

function loadMeta() {
  var m = jRead(KEY.meta, null);
  if (!m || typeof m !== 'object') m = {};
  if (!m.sources || typeof m.sources !== 'object') m.sources = {};
  return m;
}

function saveMeta(meta) { jWrite(KEY.meta, meta); }

function scriptPathOf(cfg, meta) {
  if (cfg.scriptPath && validScriptPath(cfg.scriptPath)) return cfg.scriptPath;
  if (meta && meta.argPath && validScriptPath(meta.argPath)) return meta.argPath;
  return DEFAULT_SCRIPT;
}

/* 主模块的 WebUI 与定时任务把脚本路径作为 argument 传进来，记下来供生成规则模块使用 */
function rememberArgPath(meta) {
  var arg = typeof $argument === 'string' ? $argument.trim() : '';
  if (arg && validScriptPath(arg) && meta.argPath !== arg) {
    meta.argPath = arg;
    saveMeta(meta);
  }
}

/* ------------------------------------------------------------------ */
/* 规则列表解析                                                         */
/* ------------------------------------------------------------------ */

function validEntry(t, v) {
  if (t === 'e' || t === 's') return DOMAIN_RE.test(v);
  if (t === 'k') return /^[a-z0-9_.-]{2,100}$/.test(v);
  if (t === 'w') return /^[a-z0-9_.*?-]{1,253}$/.test(v) && /[*?]/.test(v) && v.replace(/[*?.]/g, '').length >= 3;
  return false;
}

/**
 * 解析 Surge / Clash / QX 风格的规则列表，只保留域名类规则。
 * plainAsSuffix：没有类型前缀的纯域名按后缀匹配（用于手动补充的域名）。
 */
function parseRuleText(input, plainAsSuffix) {
  var d = { e: [], s: [], k: [], w: [] };
  var seen = {};
  var n = 0, skipped = 0, bad = 0;
  var lines = String(input || '').split(/\r\n|\r|\n/);

  for (var i = 0; i < lines.length; i++) {
    var line = lines[i].trim();
    if (!line) continue;
    var c0 = line.charAt(0);
    if (c0 === '#' || c0 === ';' || c0 === '!' || line.indexOf('//') === 0) continue;
    if (/^payload\s*:/i.test(line)) continue;
    if (line.indexOf('- ') === 0) line = line.slice(2).trim();
    line = line.replace(/^['"]+|['"]+$/g, '').trim();
    var sharp = line.search(/\s#/);
    if (sharp > 0) line = line.slice(0, sharp).trim();
    if (!line) continue;

    var type, val;
    if (line.indexOf(',') >= 0) {
      var parts = line.split(',');
      type = parts[0].trim().toUpperCase();
      val = (parts[1] || '').trim();
    } else if (line.indexOf('+.') === 0) {
      type = 'DOMAIN-SUFFIX'; val = line.slice(2);
    } else if (line.indexOf('*.') === 0 && !/[*?]/.test(line.slice(2))) {
      type = 'DOMAIN-SUFFIX'; val = line.slice(2);
    } else if (c0 === '.') {
      type = 'DOMAIN-SUFFIX'; val = line.slice(1);
    } else if (/[*?]/.test(line)) {
      type = 'DOMAIN-WILDCARD'; val = line;
    } else {
      type = plainAsSuffix ? 'DOMAIN-SUFFIX' : 'DOMAIN'; val = line;
    }
    val = val.toLowerCase().replace(/^\.+|\.+$/g, '');

    var t;
    switch (type) {
      case 'DOMAIN': case 'HOST': t = 'e'; break;
      case 'DOMAIN-SUFFIX': case 'HOST-SUFFIX': t = 's'; break;
      case 'DOMAIN-KEYWORD': case 'HOST-KEYWORD': t = 'k'; break;
      case 'DOMAIN-WILDCARD': case 'HOST-WILDCARD': t = 'w'; break;
      default: skipped++; continue;
    }
    if (!validEntry(t, val)) { bad++; continue; }
    var key = t + ':' + val;
    if (own(seen, key)) continue;
    seen[key] = 1;
    d[t].push(val);
    n++;
  }
  return { d: d, n: n, skipped: skipped, bad: bad };
}

function emptyDomains() { return { e: new Set(), s: new Set(), k: new Set(), w: new Set() }; }

function mergeDomains(into, d) {
  ['e', 's', 'k', 'w'].forEach(function (t) {
    var src = d[t];
    if (src && src.forEach) src.forEach(function (x) { into[t].add(x); });
  });
}

function countDomains(d) { return d.e.size + d.s.size + d.k.size + d.w.size; }

function readSource(url, memo) {
  if (memo && own(memo, url)) return memo[url];
  var c = jRead(KEY.src + hash(url), null);
  if (!c || c.url !== url || !c.d) c = null;
  if (memo) memo[url] = c;
  return c;
}

function ruleDomains(rule, memo) {
  var acc = emptyDomains();
  rule.sources.forEach(function (u) {
    var c = readSource(u, memo);
    if (c) mergeDomains(acc, c.d);
  });
  if (rule.extra) mergeDomains(acc, parseRuleText(rule.extra, true).d);
  return acc;
}

function cleanupSources(cfg, meta) {
  var used = {};
  cfg.rules.forEach(function (r) { r.sources.forEach(function (u) { used[u] = 1; }); });
  Object.keys(meta.sources).forEach(function (u) {
    if (!own(used, u)) {
      sWrite(KEY.src + hash(u), null);
      delete meta.sources[u];
    }
  });
}

/* ------------------------------------------------------------------ */
/* 参数编译                                                             */
/* ------------------------------------------------------------------ */

function compileParams(params) {
  var q = [], r = [];
  params.forEach(function (p) {
    var lc = p.name.toLowerCase();
    switch (p.where) {
      case 'resp':
        if (own(LIFE_NAMES, lc)) {
          r.push({ t: 'life', sec: Math.max(0, Math.round(Number(p.value) * UNITS[p.unit])), mode: p.mode, only: globListToRe(p.only) });
        } else if (own(FLAG_ATTRS, lc)) {
          r.push({ t: 'flag', a: FLAG_ATTRS[lc], on: !FALSY_RE.test(p.value), only: globListToRe(p.only) });
        } else {
          r.push({ t: 'attr', a: own(KNOWN_ATTRS, lc) ? KNOWN_ATTRS[lc] : p.name, v: p.value, only: globListToRe(p.only) });
        }
        break;
      case 'block':
        r.push({ t: 'block', only: globListToRe(p.name) });
        break;
      case 'req':
        q.push({ t: 'set', n: p.name, v: p.value });
        break;
      case 'reqdel':
        q.push({ t: 'del', m: globListToRe(p.name) });
        break;
    }
  });
  return { q: q, r: r };
}

/* ------------------------------------------------------------------ */
/* 运行时索引                                                           */
/* ------------------------------------------------------------------ */

function makeIndex(cfg, memo) {
  var idx = {
    v: 1, at: now(), on: !!cfg.enabled, dbg: !!cfg.debug, rules: [],
    e: Object.create(null), s: Object.create(null), k: Object.create(null), w: Object.create(null)
  };
  function put(map, key, ri) {
    var a = map[key];
    if (!a) a = map[key] = [];
    if (a[a.length - 1] !== ri) a.push(ri);
  }
  cfg.rules.forEach(function (rule) {
    if (!rule.enabled) return;
    var acts = compileParams(rule.params);
    if (!acts.q.length && !acts.r.length) return;
    var d = ruleDomains(rule, memo);
    var ri = idx.rules.length;
    idx.rules.push({ id: rule.id, name: rule.name, q: acts.q, r: acts.r });
    d.e.forEach(function (x) { put(idx.e, x, ri); });
    d.s.forEach(function (x) { put(idx.s, x, ri); });
    d.k.forEach(function (x) { put(idx.k, x, ri); });
    d.w.forEach(function (x) { put(idx.w, x, ri); });
  });
  return idx;
}

function saveIndex(cfg, memo, meta) {
  var idx = makeIndex(cfg, memo);
  var ok = jWrite(KEY.idx, idx);
  if (meta) {
    var err = ok ? '' : '受控域名太多，索引无法写入本地存储。请减少规则集里的列表。';
    if (meta.idxErr !== err) { meta.idxErr = err; saveMeta(meta); }
  }
  if (!ok) log('索引写入失败');
  return idx;
}

function loadIndex() {
  var idx = jRead(KEY.idx, null);
  if (!idx || idx.v !== 1 || !Array.isArray(idx.rules) || !idx.e || !idx.s || !idx.k || !idx.w) return null;
  return idx;
}

/** 返回命中的规则序号（按配置顺序）。detail 为 true 时同时返回命中原因。 */
function matchHost(idx, host, detail) {
  var hits = {};
  var order = [];
  function add(list, via) {
    if (!list) return;
    for (var i = 0; i < list.length; i++) {
      var ri = list[i];
      if (!own(hits, ri)) { hits[ri] = via; order.push(ri); }
    }
  }
  if (own(idx.e, host)) add(idx.e[host], detail ? '域名 ' + host : '');
  var p = host;
  while (p) {
    if (own(idx.s, p)) add(idx.s[p], detail ? '后缀 ' + p : '');
    var dot = p.indexOf('.');
    if (dot < 0) break;
    p = p.slice(dot + 1);
  }
  Object.keys(idx.k).forEach(function (kw) {
    if (host.indexOf(kw) >= 0) add(idx.k[kw], detail ? '关键词 ' + kw : '');
  });
  Object.keys(idx.w).forEach(function (w) {
    var re = hostGlobRe(w);
    if (re && re.test(host)) add(idx.w[w], detail ? '通配 ' + w : '');
  });
  order.sort(function (a, b) { return a - b; });
  return detail ? order.map(function (ri) { return { ri: ri, via: hits[ri] }; }) : order;
}

function collectActs(idx, list, side) {
  var out = [];
  list.forEach(function (ri) {
    var r = idx.rules[ri];
    if (r && Array.isArray(r[side])) out.push.apply(out, r[side]);
  });
  return out;
}

/* ------------------------------------------------------------------ */
/* Set-Cookie 处理                                                      */
/* ------------------------------------------------------------------ */

/* 对象模式下多个 Set-Cookie 可能被合并为一行，按“逗号后紧跟 name=”切开，Expires 中的逗号不受影响 */
function splitSetCookie(v) {
  return String(v).split(/,(?=\s*[^;,=\s]+=)/).map(function (s) { return s.trim(); }).filter(Boolean);
}

function parseSetCookie(s) {
  var parts = String(s).split(';');
  var first = parts.shift().trim();
  var eq = first.indexOf('=');
  var c = {
    first: first,
    name: eq >= 0 ? first.slice(0, eq).trim() : '',
    value: eq >= 0 ? first.slice(eq + 1).trim() : first,
    attrs: [],
    dirty: false
  };
  parts.forEach(function (p) {
    var i = p.indexOf('=');
    var k = (i >= 0 ? p.slice(0, i) : p).trim();
    if (!k) return;
    c.attrs.push({ k: k, lk: k.toLowerCase(), v: i >= 0 ? p.slice(i + 1).trim() : null });
  });
  return c;
}

function stringifySetCookie(c) {
  return [c.first].concat(c.attrs.map(function (a) { return a.v === null ? a.k : a.k + '=' + a.v; })).join('; ');
}

function lastAttr(c, lk) {
  for (var i = c.attrs.length - 1; i >= 0; i--) if (c.attrs[i].lk === lk) return c.attrs[i];
  return null;
}

function removeAttrs(c, lks) {
  var before = c.attrs.length;
  c.attrs = c.attrs.filter(function (a) { return lks.indexOf(a.lk) < 0; });
  return c.attrs.length !== before;
}

function parseCookieDate(s) {
  var t = Date.parse(s);
  if (isNaN(t)) t = Date.parse(String(s).replace(/-/g, ' '));
  return t;
}

/* 剩余有效秒数：null 表示会话 Cookie，NaN 表示无法解析 */
function remainingSec(c, t) {
  var ma = lastAttr(c, 'max-age');
  if (ma && ma.v !== null && /^-?\d+$/.test(ma.v)) return parseInt(ma.v, 10);
  var ex = lastAttr(c, 'expires');
  if (ex && ex.v) {
    var ts = parseCookieDate(ex.v);
    return isNaN(ts) ? NaN : Math.floor((ts - t) / 1000);
  }
  return null;
}

function applyLife(c, a, t) {
  var rem = remainingSec(c, t);
  /* 删除型 Cookie（已过期或 Max-Age<=0）和无法解析的日期一律不动，避免把已删除的 Cookie 复活 */
  if (rem !== null && (isNaN(rem) || rem <= 0)) return;
  if (rem === null && c.value === '') return;
  if (a.mode === 'cap' && (rem === null || rem <= a.sec)) return;
  removeAttrs(c, ['max-age', 'expires']);
  c.attrs.push({ k: 'Expires', lk: 'expires', v: new Date(t + a.sec * 1000).toUTCString() });
  c.attrs.push({ k: 'Max-Age', lk: 'max-age', v: String(a.sec) });
  c.dirty = true;
}

function setFlag(c, name, on) {
  var lk = name.toLowerCase();
  var has = !!lastAttr(c, lk);
  if (on && !has) { c.attrs.push({ k: name, lk: lk, v: null }); c.dirty = true; }
  if (!on && has) { removeAttrs(c, [lk]); c.dirty = true; }
}

function setAttr(c, name, value) {
  var lk = name.toLowerCase();
  var cur = lastAttr(c, lk);
  if (value === '') {
    if (removeAttrs(c, [lk])) c.dirty = true;
    return;
  }
  if (!(cur && cur.v === value && c.attrs.filter(function (a) { return a.lk === lk; }).length === 1)) {
    removeAttrs(c, [lk]);
    c.attrs.push({ k: name, lk: lk, v: value });
    c.dirty = true;
  }
  /* 浏览器会拒绝没有 Secure 的 SameSite=None */
  if (lk === 'samesite' && value.toLowerCase() === 'none') setFlag(c, 'Secure', true);
}

/** 返回改写后的字符串；返回 null 表示拦截这条 Cookie */
function applyResponseActs(str, acts, t) {
  var c = parseSetCookie(str);
  for (var i = 0; i < acts.length; i++) {
    var a = acts[i];
    if (a.only) {
      var re = getRe(a.only);
      if (!re || !re.test(c.name)) continue;
    }
    switch (a.t) {
      case 'block': return null;
      case 'life': applyLife(c, a, t); break;
      case 'flag': setFlag(c, a.a, a.on); break;
      case 'attr': setAttr(c, a.a, a.v); break;
    }
  }
  return c.dirty ? stringifySetCookie(c) : str;
}

/** 返回改写后的 Cookie 头；返回 null 表示无需改动 */
function applyRequestActs(cookieStr, acts) {
  var pairs = String(cookieStr || '').split(';').map(function (s) { return s.trim(); }).filter(Boolean).map(function (s) {
    var i = s.indexOf('=');
    return { n: i >= 0 ? s.slice(0, i).trim() : '', raw: s };
  });
  var dirty = false;
  acts.forEach(function (a) {
    if (a.t === 'del') {
      var re = getRe(a.m);
      if (!re) return;
      var before = pairs.length;
      pairs = pairs.filter(function (p) { return !re.test(p.n); });
      if (pairs.length !== before) dirty = true;
    } else if (a.t === 'set') {
      var raw = a.n + '=' + a.v;
      var found = false;
      pairs = pairs.filter(function (p) {
        if (p.n !== a.n) return true;
        if (found) { dirty = true; return false; }
        found = true;
        if (p.raw !== raw) { p.raw = raw; dirty = true; }
        return true;
      });
      if (!found) { pairs.push({ n: a.n, raw: raw }); dirty = true; }
    }
  });
  return dirty ? pairs.map(function (p) { return p.raw; }).join('; ') : null;
}

/* 规则模块把自己的版本号作为 argument 传入，用来在管理页面显示“已生效 / 需要更新” */
function noteSeen() {
  var sig = typeof $argument === 'string' ? $argument.trim() : '';
  if (!/^[a-z0-9]{4,16}$/.test(sig)) return;
  var s = jRead(KEY.seen, null);
  var t = now();
  if (s && s.sig === sig && t - s.at < 6 * 3600 * 1000) return;
  jWrite(KEY.seen, { sig: sig, at: t });
}

function onResponse() {
  var idx = loadIndex();
  if (!idx || !idx.on || !idx.rules.length) return finish({});
  noteSeen();
  var bag = new HeaderBag($response.headers);
  var raw = bag.values('set-cookie');
  if (!raw.length) return finish({});
  var host = hostOf($request && $request.url);
  if (!host) return finish({});
  var acts = collectActs(idx, matchHost(idx, host), 'r');
  if (!acts.length) return finish({});

  var t = now();
  var changed = false;
  var mod = 0, drop = 0;
  var out = [];
  raw.forEach(function (v) {
    var list = bag.isArray ? [v] : splitSetCookie(v);
    list.forEach(function (sc) {
      var res = applyResponseActs(sc, acts, t);
      if (res === null) { changed = true; drop++; return; }
      if (res !== sc) { changed = true; mod++; }
      out.push(res);
    });
  });
  if (!changed) return finish({});
  bag.replace('set-cookie', out, 'Set-Cookie');
  if (idx.dbg) log(host, '改写 Set-Cookie', mod, '条，拦截', drop, '条');
  finish({ headers: bag.output() });
}

function onRequest() {
  var idx = loadIndex();
  if (!idx || !idx.on || !idx.rules.length) return finish({});
  noteSeen();
  var host = hostOf($request.url);
  if (!host) return finish({});
  var acts = collectActs(idx, matchHost(idx, host), 'q');
  if (!acts.length) return finish({});
  var bag = new HeaderBag($request.headers);
  var next = applyRequestActs(bag.values('cookie').join('; '), acts);
  if (next === null) return finish({});
  bag.replace('cookie', next ? [next] : [], 'Cookie');
  if (idx.dbg) log(host, '改写请求 Cookie');
  finish({ headers: bag.output() });
}

/* ------------------------------------------------------------------ */
/* 规则模块生成                                                         */
/* ------------------------------------------------------------------ */

function coveredBySuffix(set, host) {
  var p = host;
  while (true) {
    if (set.has(p)) return true;
    var i = p.indexOf('.');
    if (i < 0) return false;
    p = p.slice(i + 1);
  }
}

/* 去掉被其它条目覆盖的冗余项，缩短匹配表达式和 MITM 列表 */
function compactDomains(d) {
  var k = [];
  Array.from(d.k).sort(function (a, b) { return a.length - b.length || (a < b ? -1 : 1); }).forEach(function (x) {
    if (!k.some(function (y) { return x.indexOf(y) >= 0; })) k.push(x);
  });
  function hitKw(x) { return k.some(function (y) { return x.indexOf(y) >= 0; }); }
  var sset = new Set();
  Array.from(d.s).filter(function (x) { return !hitKw(x); }).sort(function (a, b) {
    return a.split('.').length - b.split('.').length || (a < b ? -1 : 1);
  }).forEach(function (x) { if (!coveredBySuffix(sset, x)) sset.add(x); });
  var e = Array.from(d.e).filter(function (x) { return !hitKw(x) && !coveredBySuffix(sset, x); }).sort();
  return { e: e, s: Array.from(sset).sort(), k: k.sort(), w: Array.from(d.w).sort() };
}

/* 生成的表达式里不含逗号、空格、引号和 #，可以直接写进模块行 */
function buildPattern(c) {
  var alts = [];
  if (c.s.length) alts.push('(?:' + HOST_CH + '+\\.)?(?:' + c.s.map(escRe).join('|') + ')');
  if (c.e.length) alts.push('(?:' + c.e.map(escRe).join('|') + ')');
  if (c.k.length) alts.push(HOST_CH + '*(?:' + c.k.map(escRe).join('|') + ')' + HOST_CH + '*');
  c.w.forEach(function (w) {
    alts.push(w.split('').map(function (ch) {
      if (ch === '*') return HOST_CH + '*';
      if (ch === '?') return HOST_CH;
      return escRe(ch);
    }).join(''));
  });
  if (!alts.length) return '';
  return '^https?:\\/\\/(?:' + alts.join('|') + ')(?::\\d+)?(?:[\\/?]|$)';
}

function parseExcludes(text) {
  return String(text || '').split(/[\s,，]+/).map(function (x) {
    return x.trim().toLowerCase().replace(/^-+/, '');
  }).filter(function (x) {
    return /^[a-z0-9_.*?:-]+$/.test(x) && x.replace(/[*?.:-]/g, '').length > 0;
  });
}

function mitmHosts(c, excludeText) {
  var out = [];
  var seen = {};
  function add(x) { if (x && !own(seen, x)) { seen[x] = 1; out.push(x); } }
  parseExcludes(excludeText).forEach(function (x) { add('-' + x); });
  c.s.forEach(function (x) { add('*.' + x); add(x); });
  c.e.forEach(add);
  c.k.forEach(function (x) { add('*' + x + '*'); });
  c.w.forEach(add);
  return out;
}

function hostListMatch(list, host) {
  for (var i = 0; i < list.length; i++) {
    var item = list[i];
    var neg = item.charAt(0) === '-';
    var pat = neg ? item.slice(1) : item;
    var re = hostGlobRe(pat);
    if (re && re.test(host)) return !neg;
  }
  return false;
}

function genModule(cfg, scriptPath, memo) {
  var req = emptyDomains(), resp = emptyDomains(), all = emptyDomains();
  var rules = 0;
  cfg.rules.forEach(function (rule) {
    if (!rule.enabled) return;
    var acts = compileParams(rule.params);
    if (!acts.q.length && !acts.r.length) return;
    var d = ruleDomains(rule, memo);
    if (acts.q.length) mergeDomains(req, d);
    if (acts.r.length) mergeDomains(resp, d);
    mergeDomains(all, d);
    rules++;
  });

  var reqPattern = buildPattern(compactDomains(req));
  var respPattern = buildPattern(compactDomains(resp));
  var hostList = mitmHosts(compactDomains(all), cfg.mitmExclude);
  var domains = countDomains(all);

  var body = [];
  if (reqPattern || respPattern) {
    body.push('[Script]');
    if (reqPattern) {
      body.push('CookieCtl-Req = type=http-request,pattern=' + reqPattern +
        ',requires-body=false,full-header-mode=true,timeout=5,script-path=' + scriptPath + ',argument=@SIG@');
    }
    if (respPattern) {
      body.push('CookieCtl-Resp = type=http-response,pattern=' + respPattern +
        ',requires-body=false,full-header-mode=true,timeout=5,script-path=' + scriptPath + ',argument=@SIG@');
    }
    body.push('');
    body.push('[MITM]');
    body.push('hostname = %APPEND% ' + hostList.join(', '));
  }
  var core = body.join('\n');
  var sig = core ? (hash(core) + hash('~' + core)).slice(0, 12) : '';
  core = core.split('@SIG@').join(sig);

  var head = core
    ? ['#!name=Cookie 管控台规则',
      '#!desc=覆盖 ' + domains + ' 个域名（版本 ' + sig + '）。规则变化后请在 http://' + UI_HOST + ' 重新复制。']
    : ['#!name=Cookie 管控台规则', '#!desc=当前没有启用的规则集。'];

  return {
    text: head.join('\n') + '\n\n' + core + (core ? '\n' : ''),
    sig: sig,
    empty: !core,
    domains: domains,
    rules: rules,
    hostList: hostList,
    reqPattern: reqPattern,
    respPattern: respPattern
  };
}

/* ------------------------------------------------------------------ */
/* 下载域名列表                                                          */
/* ------------------------------------------------------------------ */

function httpGet(url, policy, timeoutSec) {
  return new Promise(function (resolve) {
    var settled = false;
    function done(v) { if (!settled) { settled = true; resolve(v); } }
    setTimeout(function () { done({ err: '超时' }); }, (timeoutSec + 3) * 1000);
    var opt = {
      url: url,
      timeout: timeoutSec,
      headers: { 'User-Agent': 'Surge-CookieCtl/' + VERSION, 'Accept': 'text/plain, */*' },
      'auto-cookie': false
    };
    if (policy) opt.policy = policy;
    try {
      $httpClient.get(opt, function (err, resp, data) {
        if (err) return done({ err: String(err) });
        done({ status: resp ? Number(resp.status || resp.statusCode || 0) : 0, data: data });
      });
    } catch (e) {
      done({ err: String((e && e.message) || e) });
    }
  });
}

async function fetchSource(url, policy) {
  var r = await httpGet(url, policy, LIMIT.fetchTimeout);
  if (r.err || r.status >= 500 || r.status === 429) r = await httpGet(url, policy, LIMIT.fetchTimeout);
  if (r.err) return { ok: false, err: '下载失败（' + r.err + '）' };
  if (r.status !== 200) return { ok: false, err: '服务器返回 HTTP ' + r.status };
  var body = typeof r.data === 'string' ? r.data : '';
  if (!body.trim()) return { ok: false, err: '下载到的内容为空' };
  if (/^\s*</.test(body) && /<html|<!doctype/i.test(body.slice(0, 1024))) {
    return { ok: false, err: '地址返回的是网页而不是规则列表，请使用 raw 地址' };
  }
  var p = parseRuleText(body, false);
  if (!p.n) {
    return { ok: false, err: p.skipped ? '列表里没有域名规则（已忽略 ' + p.skipped + ' 条其它类型的规则）' : '没有识别到可用的域名规则' };
  }
  return { ok: true, d: p.d, n: p.n, skipped: p.skipped };
}

async function pool(items, size, fn) {
  var i = 0;
  async function worker() {
    while (i < items.length) {
      var k = i++;
      try { await fn(items[k]); } catch (e) { log('任务出错', (e && e.message) || e); }
    }
  }
  var workers = [];
  for (var w = 0; w < Math.min(size, items.length); w++) workers.push(worker());
  await Promise.all(workers);
}

function withDeadline(promise, ms) {
  return new Promise(function (resolve) {
    var done = false;
    setTimeout(function () { if (!done) { done = true; resolve({ timeout: true }); } }, ms);
    promise.then(function (v) {
      if (!done) { done = true; resolve(v); }
    }, function (e) {
      if (!done) { done = true; resolve({ error: String((e && e.message) || e) }); }
    });
  });
}

/**
 * opt.force：重新下载所有相关列表；否则只下载还没有缓存的列表
 * opt.rule：只处理这个规则集（即使它被停用）
 * 下载失败时保留上一次成功的缓存。
 */
async function refreshSources(cfg, meta, opt) {
  opt = opt || {};
  var urls = [];
  cfg.rules.forEach(function (r) {
    if (opt.rule ? r.id !== opt.rule : !r.enabled) return;
    r.sources.forEach(function (u) { if (urls.indexOf(u) < 0) urls.push(u); });
  });
  if (!opt.force) urls = urls.filter(function (u) { return !readSource(u); });

  var report = { total: urls.length, ok: 0, failed: [], changed: false };
  await pool(urls, LIMIT.fetchConcurrency, async function (u) {
    var m = meta.sources[u] || (meta.sources[u] = {});
    m.tried = now();
    var r = await fetchSource(u, cfg.policy);
    if (r.ok) {
      var prev = readSource(u);
      var record = { url: u, at: now(), d: r.d };
      if (jWrite(KEY.src + hash(u), record)) {
        if (!prev || JSON.stringify(prev.d) !== JSON.stringify(r.d)) report.changed = true;
        m.ok = true; m.at = record.at; m.n = r.n; m.skipped = r.skipped; m.err = '';
        report.ok++;
        return;
      }
      r = { ok: false, err: '列表太大，无法保存到本地' };
    }
    m.ok = false;
    m.err = r.err;
    report.failed.push({ url: u, err: r.err });
  });
  return report;
}

/* ------------------------------------------------------------------ */
/* 定时任务                                                             */
/* ------------------------------------------------------------------ */

function notify(title, sub, body) {
  try { $notification.post(title, sub, body, { url: 'http://' + UI_HOST + '/' }); } catch (e) { /* 忽略 */ }
}

async function onCron() {
  var cfg = loadConfig();
  var meta = loadMeta();
  rememberArgPath(meta);
  var hasSources = cfg.rules.some(function (r) { return r.enabled && r.sources.length; });
  var due = !meta.lastRun || now() - meta.lastRun >= cfg.interval * 3600 * 1000 - 5 * 60 * 1000;
  if (!hasSources || !due) return finish();

  var path = scriptPathOf(cfg, meta);
  var before = genModule(cfg, path, {}).sig;
  var rep = await withDeadline(refreshSources(cfg, meta, { force: true }), 100 * 1000);
  meta.lastRun = now();
  saveMeta(meta);
  var memo = {};
  saveIndex(cfg, memo, meta);
  var after = genModule(cfg, path, memo).sig;
  log('定时更新完成', JSON.stringify(rep.failed ? { ok: rep.ok, failed: rep.failed.length } : rep));

  if (cfg.notify) {
    if (rep.failed && rep.failed.length) {
      notify('Cookie 管控台', rep.failed.length + ' 个域名列表更新失败', '会继续使用上一次下载的内容，点按查看详情。');
    }
    var seen = jRead(KEY.seen, null);
    if (after && after !== before && seen && seen.sig === before) {
      notify('Cookie 管控台', '域名列表有变化', '点按打开管控台，重新复制规则模块后新增的域名才会生效。');
    }
  }
  finish();
}

/* ------------------------------------------------------------------ */
/* 管理页面与接口                                                        */
/* ------------------------------------------------------------------ */

function reply(status, body, type, extra) {
  var headers = {
    'Content-Type': type,
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer'
  };
  if (extra) Object.keys(extra).forEach(function (k) { headers[k] = extra[k]; });
  finish({ response: { status: status, headers: headers, body: body } });
}

function replyJSON(status, obj) {
  reply(status, JSON.stringify(obj), 'application/json; charset=utf-8');
}

/* 写操作必须带自定义头，并且来源是管理页面本身，阻止其它网页跨站修改配置 */
function sameOrigin() {
  var bag = new HeaderBag($request.headers);
  if (bag.values('x-cookiectl')[0] !== '1') return false;
  var origin = bag.values('origin')[0];
  if (origin && origin !== 'null') {
    var re = new RegExp('^https?://' + escRe(UI_HOST) + '(?::\\d+)?$', 'i');
    if (!re.test(origin)) return false;
  }
  return true;
}

function parseBody() {
  var b = $request.body;
  if (b == null || b === '') return {};
  if (typeof b !== 'string') {
    try { b = utf8Decode(b); } catch (e) { return undefined; }
  }
  try {
    var v = JSON.parse(b);
    return v && typeof v === 'object' ? v : undefined;
  } catch (e) { return undefined; }
}

function srcInfo(url, m) {
  m = m || {};
  return {
    url: url,
    ok: m.ok === true,
    at: m.at || 0,
    tried: m.tried || 0,
    n: m.n || 0,
    skipped: m.skipped || 0,
    err: m.err || ''
  };
}

function buildState(cfg, meta, warnings, memo) {
  memo = memo || {};
  var path = scriptPathOf(cfg, meta);
  var mod = genModule(cfg, path, memo);
  return {
    version: VERSION,
    host: UI_HOST,
    now: now(),
    cfg: cfg,
    scriptPath: path,
    defaultScriptPath: (meta.argPath && validScriptPath(meta.argPath)) ? meta.argPath : DEFAULT_SCRIPT,
    rules: cfg.rules.map(function (r) {
      return {
        id: r.id,
        count: countDomains(ruleDomains(r, memo)),
        sources: r.sources.map(function (u) { return srcInfo(u, meta.sources[u]); })
      };
    }),
    module: {
      text: mod.text,
      sig: mod.sig,
      empty: mod.empty,
      domains: mod.domains,
      rules: mod.rules,
      hosts: mod.hostList.length
    },
    seen: jRead(KEY.seen, null),
    lastRun: meta.lastRun || 0,
    indexError: meta.idxErr || '',
    warnings: warnings || []
  };
}

function testURL(cfg, meta, input) {
  var url = String(input || '').trim();
  if (!url) return { error: '请输入要测试的网址' };
  if (!/^[a-z][a-z0-9+.-]*:\/\//i.test(url)) url = 'https://' + url;
  var host = hostOf(url);
  if (!host) return { error: '无法识别这个网址' };
  if (!/[\/?]/.test(url.replace(/^[a-z][a-z0-9+.-]*:\/\//i, ''))) url += '/';

  var memo = {};
  var idx = makeIndex(cfg, memo);
  var hits = matchHost(idx, host, true);
  var mod = genModule(cfg, scriptPathOf(cfg, meta), memo);
  var needReq = hits.some(function (h) { return idx.rules[h.ri].q.length > 0; });
  var needResp = hits.some(function (h) { return idx.rules[h.ri].r.length > 0; });
  var inReq = !!(mod.reqPattern && getRe(mod.reqPattern) && getRe(mod.reqPattern).test(url));
  var inResp = !!(mod.respPattern && getRe(mod.respPattern) && getRe(mod.respPattern).test(url));
  var seen = jRead(KEY.seen, null);

  return {
    url: url,
    host: host,
    https: /^https:/i.test(url),
    enabled: cfg.enabled,
    rules: hits.map(function (h) { return { id: idx.rules[h.ri].id, name: idx.rules[h.ri].name, via: h.via }; }),
    covered: (!needReq || inReq) && (!needResp || inResp),
    mitm: hostListMatch(mod.hostList, host),
    moduleCurrent: !!(seen && seen.sig === mod.sig)
  };
}

async function serveAPI(method, path, meta) {
  var cfg, warn, rep, memo;

  if (method === 'GET' && path === '/api/state') {
    return replyJSON(200, buildState(loadConfig(), meta, []));
  }
  if (method !== 'POST') return replyJSON(405, { error: '不支持的请求方式' });
  if (!sameOrigin()) return replyJSON(403, { error: '请求被拒绝：只接受来自管理页面的操作' });
  var body = parseBody();
  if (body === undefined) return replyJSON(400, { error: '请求内容不是有效的 JSON' });

  switch (path) {
    case '/api/config':
      if (!body.config || typeof body.config !== 'object') return replyJSON(400, { error: '缺少配置内容' });
      warn = [];
      cfg = normalizeConfig(body.config, warn);
      if (!jWrite(KEY.cfg, cfg)) return replyJSON(500, { error: '配置保存失败，本地存储可能已满' });
      cleanupSources(cfg, meta);
      rep = await withDeadline(refreshSources(cfg, meta, {}), 45 * 1000);
      saveMeta(meta);
      memo = {};
      saveIndex(cfg, memo, meta);
      return replyJSON(200, { ok: true, report: rep, state: buildState(cfg, meta, warn, memo) });

    case '/api/refresh':
      cfg = loadConfig();
      var rule = typeof body.rule === 'string' && body.rule ? body.rule : '';
      rep = await withDeadline(refreshSources(cfg, meta, { force: true, rule: rule }), 50 * 1000);
      if (!rule) meta.lastRun = now();
      saveMeta(meta);
      memo = {};
      saveIndex(cfg, memo, meta);
      return replyJSON(200, { ok: true, report: rep, state: buildState(cfg, meta, [], memo) });

    case '/api/test':
      return replyJSON(200, testURL(loadConfig(), meta, body.url));

    case '/api/reset':
      cfg = defaultConfig();
      jWrite(KEY.cfg, cfg);
      cleanupSources(cfg, meta);
      rep = await withDeadline(refreshSources(cfg, meta, {}), 45 * 1000);
      saveMeta(meta);
      memo = {};
      saveIndex(cfg, memo, meta);
      return replyJSON(200, { ok: true, report: rep, state: buildState(cfg, meta, [], memo) });
  }
  return replyJSON(404, { error: '接口不存在' });
}

async function serveUI() {
  var method = String($request.method || 'GET').toUpperCase();
  var path = pathOf($request.url);
  try {
    var meta = loadMeta();
    rememberArgPath(meta);

    if (method === 'OPTIONS' || path === '/favicon.ico') return reply(204, '', 'text/plain');

    if (method === 'GET' && (path === '/' || path === '/index.html')) {
      return reply(200, pageHTML(), 'text/html; charset=utf-8', {
        'Content-Security-Policy': "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; " +
          "connect-src 'self'; img-src 'self' data: blob:; base-uri 'none'; form-action 'none'; frame-ancestors 'none'"
      });
    }

    if (method === 'GET' && path === '/rules.sgmodule') {
      var cfg = loadConfig();
      var mod = genModule(cfg, scriptPathOf(cfg, meta), {});
      return reply(200, mod.text, 'text/plain; charset=utf-8', {
        'Content-Disposition': 'inline; filename="CookieCtl-Rules.sgmodule"'
      });
    }

    if (path.indexOf('/api/') === 0) return await serveAPI(method, path, meta);

    return reply(302, '', 'text/plain', { Location: 'http://' + UI_HOST + '/' });
  } catch (e) {
    log('管理页面出错', (e && e.stack) || e);
    return replyJSON(500, { error: '处理请求时出错：' + ((e && e.message) || e) });
  }
}

/* ------------------------------------------------------------------ */
/* 入口                                                                */
/* ------------------------------------------------------------------ */

(function main() {
  var hasReq = typeof $request !== 'undefined' && $request && typeof $request === 'object';
  var hasResp = typeof $response !== 'undefined' && $response && typeof $response === 'object';
  var isUI = hasReq && !hasResp && hostOf($request.url) === UI_HOST;
  try {
    if (isUI) {
      serveUI().catch(function (e) { replyJSON(500, { error: String((e && e.message) || e) }); });
    } else if (hasResp) {
      onResponse();
    } else if (hasReq) {
      onRequest();
    } else {
      onCron().catch(function (e) { log('定时任务出错', (e && e.stack) || e); finish(); });
    }
  } catch (e) {
    log('脚本出错', (e && e.stack) || e);
    if (isUI) replyJSON(500, { error: String((e && e.message) || e) });
    else finish({});
  }
})();

/* ------------------------------------------------------------------ */
/* 管理页面                                                             */
/* ------------------------------------------------------------------ */

function pageHTML() {
  return String.raw`<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="light dark">
<meta name="theme-color" content="#EDF0F3" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#10151B" media="(prefers-color-scheme: dark)">
<meta name="format-detection" content="telephone=no">
<title>Cookie 管控台</title>
<style>
:root{
  --bg:#EDF0F3; --surface:#FFFFFF; --surface-2:#F4F6F8; --ink:#17202A; --ink-2:#56616F; --ink-3:#8A95A3;
  --line:#D6DCE3; --line-2:#E6EAEF;
  --teal:#0D6B67; --teal-ink:#FFFFFF; --teal-soft:#DCEFED;
  --crumb:#F6E6CC; --crumb-ink:#6E430D; --crumb-edge:#E3C38C;
  --danger:#B23A2C; --danger-soft:#F8E1DD;
  --warn:#86560A; --warn-soft:#FBEFD8;
  --r-lg:16px; --r-md:11px; --r-sm:8px;
  --font:-apple-system,BlinkMacSystemFont,"SF Pro Text","PingFang SC","Hiragino Sans GB","Microsoft YaHei","Segoe UI",sans-serif;
  --round:ui-rounded,"SF Pro Rounded",-apple-system,BlinkMacSystemFont,"PingFang SC","Microsoft YaHei",sans-serif;
  --mono:ui-monospace,"SF Mono",Menlo,Consolas,"Liberation Mono",monospace;
}
@media (prefers-color-scheme: dark){
  :root{
    --bg:#10151B; --surface:#171E26; --surface-2:#1E2731; --ink:#E6EBF0; --ink-2:#A1ACB9; --ink-3:#6F7C8B;
    --line:#2B3643; --line-2:#232D38;
    --teal:#4DBDB3; --teal-ink:#06201F; --teal-soft:#16363A;
    --crumb:#3A2C18; --crumb-ink:#F2C47E; --crumb-edge:#5C4524;
    --danger:#F0806F; --danger-soft:#3A1F1C;
    --warn:#F0BE68; --warn-soft:#352A16;
  }
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 var(--font);-webkit-font-smoothing:antialiased;padding-bottom:calc(110px + env(safe-area-inset-bottom))}
button,input,select,textarea{font:inherit;color:inherit;letter-spacing:inherit}
:focus-visible{outline:2px solid var(--teal);outline-offset:2px}
.wrap{max-width:760px;margin:0 auto;padding:calc(22px + env(safe-area-inset-top)) max(16px,env(safe-area-inset-right)) 24px max(16px,env(safe-area-inset-left))}
.mono{font-family:var(--mono);font-size:.92em}
.sp{flex:1}
.boot{color:var(--ink-2);padding:40px 0}
.ic{display:inline-flex;width:16px;height:16px;flex:none}
.ic svg{width:100%;height:100%}

/* 页头 */
.top{display:flex;align-items:center;gap:12px}
.mark{width:42px;height:42px;flex:none}
.mark svg{width:100%;height:100%;display:block}
.mk-body{fill:var(--crumb);stroke:var(--crumb-edge);stroke-width:2}
.mk-chip{fill:var(--crumb-ink)}
.title{font-family:var(--round);font-weight:800;font-size:27px;letter-spacing:-.01em;line-height:1.15;margin:0}
.status{margin:16px 0 0;font-size:17px;line-height:1.6;max-width:34em}
.status b{font-family:var(--round);font-weight:800;font-variant-numeric:tabular-nums}
.pill{display:inline-flex;align-items:center;gap:6px;padding:2px 10px 2px 9px;border-radius:999px;font-size:13px;font-weight:600;white-space:nowrap;text-decoration:none;vertical-align:1px}
.pill i{width:7px;height:7px;border-radius:50%;background:currentColor;flex:none}
.pill.ok{background:var(--teal-soft);color:var(--teal)}
.pill.warn{background:var(--warn-soft);color:var(--warn)}
.pill.idle{background:var(--surface);color:var(--ink-2);box-shadow:inset 0 0 0 1px var(--line)}

/* 分区 */
.sec{margin-top:38px}
.sec-h{display:flex;align-items:center;gap:8px;margin:0 0 12px;flex-wrap:wrap}
.sec-h h2{font-family:var(--round);font-size:20px;font-weight:800;margin:0;letter-spacing:-.005em}
.sec-note{color:var(--ink-2);font-size:14px;margin:-4px 0 14px;max-width:38em}

/* 按钮 */
.btn{text-decoration:none;appearance:none;-webkit-appearance:none;border:1px solid var(--line);background:var(--surface);border-radius:var(--r-md);padding:7px 14px;font-weight:600;font-size:14px;line-height:1.3;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;gap:6px;min-height:38px;transition:background-color .15s,border-color .15s,opacity .15s;white-space:nowrap}
.btn:hover{border-color:var(--ink-3)}
.btn:active{transform:translateY(1px)}
.btn.primary{background:var(--teal);border-color:var(--teal);color:var(--teal-ink)}
.btn.primary:hover{filter:brightness(1.06)}
.btn.ghost{background:transparent;border-color:transparent;color:var(--ink-2)}
.btn.ghost:hover{background:var(--surface-2)}
.btn.danger{background:transparent;border-color:transparent;color:var(--danger)}
.btn.danger:hover{background:var(--danger-soft)}
.btn.dashed{border-style:dashed;background:transparent;color:var(--ink-2)}
.btn.sm{min-height:32px;padding:4px 11px;font-size:13px}
.btn[disabled]{opacity:.45;pointer-events:none}
.icon-btn{appearance:none;border:0;background:transparent;color:var(--ink-3);width:36px;height:36px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;cursor:pointer;flex:none}
.icon-btn:hover{background:var(--line-2);color:var(--danger)}
.spin{width:14px;height:14px;border:2px solid currentColor;border-right-color:transparent;border-radius:50%;animation:spin .7s linear infinite;flex:none}
@keyframes spin{to{transform:rotate(360deg)}}

/* 开关 */
.sw{position:relative;display:inline-block;width:51px;height:31px;flex:none}
.sw input{position:absolute;inset:0;width:100%;height:100%;opacity:0;margin:0;cursor:pointer;z-index:1}
.sw span{position:absolute;inset:0;border-radius:999px;background:var(--line);transition:background-color .2s}
.sw span::after{content:"";position:absolute;top:2px;left:2px;width:27px;height:27px;border-radius:50%;background:#fff;box-shadow:0 2px 5px rgba(0,0,0,.22);transition:transform .2s}
.sw input:checked + span{background:var(--teal)}
.sw input:checked + span::after{transform:translateX(20px)}
.sw input:focus-visible + span{outline:2px solid var(--teal);outline-offset:2px}

/* 规则集 */
.rule{background:var(--surface);border:1px solid var(--line-2);border-radius:var(--r-lg);margin-bottom:12px;position:relative;overflow:hidden}
.rule::before{content:"";position:absolute;left:0;top:0;bottom:0;width:4px;background:var(--teal);transition:background-color .2s}
.rule.off::before{background:var(--line)}
.rule.off .rule-name{color:var(--ink-3)}
.rule.off .crumbs{opacity:.55}
.rule-head{display:flex;align-items:center;gap:12px;padding:13px 12px 10px 18px}
.rule-tap{flex:1;min-width:0;appearance:none;background:none;border:0;padding:6px 4px;margin:-6px 0;text-align:left;cursor:pointer;display:flex;align-items:center;gap:10px;border-radius:var(--r-sm)}
.rule-title{display:flex;flex-direction:column;min-width:0;flex:1;gap:1px}
.rule-name{font-weight:700;font-size:16.5px;line-height:1.35;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-width:0}
.rule-meta{color:var(--ink-2);font-size:12.5px;line-height:1.4;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-variant-numeric:tabular-nums}
.rule-meta.bad{color:var(--danger)}
.chev{color:var(--ink-3);transition:transform .2s}
.rule.open .chev{transform:rotate(180deg)}
.crumbs{display:flex;flex-wrap:wrap;gap:6px;padding:0 14px 14px 81px}
.crumb{display:inline-flex;align-items:baseline;gap:5px;background:var(--crumb);color:var(--crumb-ink);border:1px solid var(--crumb-edge);border-radius:999px;padding:3px 11px;font:600 13px/1.4 var(--round);max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.crumb b{font-weight:800;font-size:14px;font-variant-numeric:tabular-nums}
.crumb.req{background:transparent}
.crumb.none{background:transparent;border-style:dashed;border-color:var(--line);color:var(--ink-3)}
.rule-body{border-top:1px solid var(--line-2);padding:18px 16px 16px 20px;display:grid;gap:20px}

/* 表单 */
.field{min-width:0}
.lbl{display:block;font-weight:650;font-size:13.5px;color:var(--ink);margin-bottom:7px}
.inp{width:100%;border:1px solid var(--line);background:var(--surface-2);border-radius:var(--r-sm);padding:8px 11px;font-size:15px;min-height:40px;outline:none;transition:border-color .15s,background-color .15s;-webkit-appearance:none;appearance:none}
.inp:focus{border-color:var(--teal);background:var(--surface)}
.inp::placeholder{color:var(--ink-3)}
textarea.inp{resize:vertical;min-height:76px;font-family:var(--mono);font-size:13px;line-height:1.55;display:block}
select.inp{padding-right:30px;background-image:linear-gradient(45deg,transparent 50%,var(--ink-3) 50%),linear-gradient(135deg,var(--ink-3) 50%,transparent 50%);background-position:calc(100% - 15px) 50%,calc(100% - 10px) 50%;background-size:5px 5px,5px 5px;background-repeat:no-repeat;cursor:pointer}
@media (pointer:coarse){.inp,textarea.inp{font-size:16px}}
.hint{color:var(--ink-2);font-size:12.5px;line-height:1.55;margin:7px 0 0;max-width:46em}
.row-actions{display:flex;gap:8px;margin-top:10px;flex-wrap:wrap}

/* 列表状态 */
.srcs{list-style:none;margin:10px 0 0;padding:0;display:grid;gap:8px}
.src{display:flex;gap:9px;align-items:flex-start;font-size:13px;color:var(--ink-2);line-height:1.5}
.src-url{font-family:var(--mono);font-size:12px;color:var(--ink);word-break:break-all}
.dot{width:8px;height:8px;border-radius:50%;margin-top:6px;flex:none;background:var(--ink-3)}
.dot.ok{background:var(--teal)}
.dot.bad{background:var(--danger)}
.dot.wait{background:var(--crumb-edge)}

/* 参数 */
.params{display:grid;gap:10px}
.param{border:1px solid var(--line-2);background:var(--surface-2);border-radius:var(--r-md);padding:10px 10px 12px 12px;display:grid;gap:10px}
.param-top{display:flex;gap:6px;align-items:center}
.param-top .inp{flex:1;background-color:var(--surface);font-weight:600}
.param-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.param-grid.one{grid-template-columns:1fr}
.mini{display:flex;flex-direction:column;gap:4px;min-width:0}
.mini > span{font-size:12px;color:var(--ink-2);font-weight:600}
.mini .inp{background-color:var(--surface)}
.param-desc{margin:0;font-size:13px;color:var(--crumb-ink);background:var(--crumb);border-radius:var(--r-sm);padding:7px 10px;line-height:1.5}
.quick{display:flex;flex-wrap:wrap;gap:6px;margin-top:10px}
.rule-foot{display:flex;align-items:center;gap:4px;flex-wrap:wrap;margin:-4px -8px -6px}

/* 面板与提示 */
.panel{background:var(--surface);border:1px solid var(--line-2);border-radius:var(--r-lg);padding:16px}
.notice{display:flex;align-items:flex-start;gap:10px;background:var(--warn-soft);color:var(--warn);border-radius:var(--r-md);padding:10px 14px;font-size:14px;line-height:1.5;margin:0 0 12px}
.notice.err{background:var(--danger-soft);color:var(--danger)}
.notice.ok{background:var(--teal-soft);color:var(--teal)}
.notice ul{margin:4px 0 0;padding-left:18px}
.notice .sp{flex:1}
.top-notices{margin-top:18px}
.mod-status{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:6px}
.mod-facts{color:var(--ink-2);font-size:13.5px}
.steps{counter-reset:s;list-style:none;padding:0;margin:14px 0;display:grid;gap:9px}
.steps li{counter-increment:s;display:flex;gap:10px;font-size:14px;line-height:1.5}
.steps li::before{content:counter(s);flex:none;width:22px;height:22px;border-radius:50%;background:var(--teal-soft);color:var(--teal);font:800 12px/22px var(--round);text-align:center;margin-top:-1px}
.actions{display:flex;gap:8px;flex-wrap:wrap}
pre.code{margin:14px 0 0;max-height:300px;overflow:auto;background:var(--surface-2);border:1px solid var(--line-2);border-radius:var(--r-md);padding:12px;font:12px/1.6 var(--mono);white-space:pre-wrap;word-break:break-all;-webkit-user-select:text;user-select:text}

/* 测试 */
.test-row{display:flex;gap:8px}
.test-row .inp{flex:1;font-family:var(--mono);font-size:14px}
.result{margin-top:14px;display:grid;gap:10px}
.result > p{margin:0}
.hit{background:var(--surface);border:1px solid var(--line-2);border-radius:var(--r-md);padding:10px 14px}
.hit-h{display:flex;gap:8px;align-items:baseline;flex-wrap:wrap}
.hit-via{color:var(--ink-2);font-size:13px;font-family:var(--mono)}
.hit ul{margin:6px 0 0;padding-left:18px;font-size:14px;color:var(--ink-2)}
.checks{display:grid;gap:4px;font-size:13.5px}
.check{display:flex;gap:8px;align-items:flex-start}
.check .dot{margin-top:7px}

/* 设置分组 */
.group{background:var(--surface);border:1px solid var(--line-2);border-radius:var(--r-lg);overflow:hidden}
.group + .group{margin-top:14px}
.row{display:flex;align-items:center;gap:14px;padding:12px 16px;min-height:56px}
.row + .row{border-top:1px solid var(--line-2)}
.row .k{flex:1;min-width:0}
.row .k > div{font-weight:600}
.row .k small{display:block;color:var(--ink-2);font-size:12.5px;line-height:1.5;margin-top:2px}
.row > .inp{width:auto;max-width:48%}
.row.col{flex-direction:column;align-items:stretch;gap:8px}
.row.col .inp{width:100%;max-width:none}
.file-hidden{position:absolute;width:1px;height:1px;opacity:0;pointer-events:none}

.empty{background:var(--surface);border:1px dashed var(--line);border-radius:var(--r-lg);padding:22px;text-align:left}
.empty p{margin:0 0 14px;color:var(--ink-2);max-width:34em}
.foot{margin-top:36px;color:var(--ink-3);font-size:12.5px}

/* 保存栏与提示 */
.savebar{position:fixed;left:50%;bottom:calc(14px + env(safe-area-inset-bottom));transform:translate(-50%,160%);width:min(728px,calc(100% - 24px));background:var(--ink);color:var(--bg);border-radius:15px;padding:8px 8px 8px 18px;display:flex;align-items:center;gap:6px;box-shadow:0 14px 34px -12px rgba(0,0,0,.5);transition:transform .28s cubic-bezier(.2,.8,.2,1),visibility 0s .28s;visibility:hidden;z-index:20}
.savebar.show{transform:translate(-50%,0);visibility:visible;transition:transform .28s cubic-bezier(.2,.8,.2,1)}
.savebar .msg{flex:1;font-weight:650;font-size:14px}
.savebar .btn.ghost{color:var(--bg);opacity:.8}
.savebar .btn.ghost:hover{background:rgba(127,127,127,.18)}
.savebar .btn.primary{min-width:112px}
.toast{position:fixed;left:50%;top:calc(12px + env(safe-area-inset-top));transform:translate(-50%,-180%);max-width:calc(100% - 32px);background:var(--surface);color:var(--ink);border:1px solid var(--line);border-left:4px solid var(--teal);border-radius:12px;padding:10px 16px;font-size:14px;font-weight:600;box-shadow:0 12px 30px -14px rgba(0,0,0,.35);transition:transform .25s cubic-bezier(.2,.8,.2,1);z-index:30}
.toast.show{transform:translate(-50%,0)}
.toast.err{border-left-color:var(--danger)}
.toast.warn{border-left-color:var(--warn)}

@media (min-width:640px){
  .param-grid.life{grid-template-columns:1fr 1fr 1fr 1fr}
  .title{font-size:30px}
}
@media (max-width:420px){
  .crumbs{padding-left:18px}
  .row{flex-wrap:wrap}
  .row > .inp{max-width:100%;width:100%}
}
@media (prefers-reduced-motion: reduce){
  *{transition:none!important;scroll-behavior:auto!important}
}
</style>
</head>
<body>
<div id="app" class="wrap"><p class="boot">正在载入…</p></div>
<div id="savebar" class="savebar" aria-hidden="true"></div>
<div id="toast" class="toast" role="status" aria-live="polite"></div>
<datalist id="attr-names">
  <option value="expires">有效期</option>
  <option value="max-age">有效期</option>
  <option value="SameSite">Lax / Strict / None</option>
  <option value="Secure">仅 HTTPS 发送</option>
  <option value="HttpOnly">禁止脚本读取</option>
  <option value="Domain">作用域名</option>
  <option value="Path">作用路径</option>
</datalist>
<script>
(function () {
'use strict';

var S = { srv: null, draft: null, base: '', open: {}, busy: '', test: null, testInput: '', showModule: false, warnings: [], loadError: '', barState: '' };
var UNIT = { s: '秒', m: '分钟', h: '小时', d: '天' };
var WHERE = [['resp', '改写响应 Cookie 属性'], ['block', '拦截响应 Cookie'], ['req', '设置请求 Cookie'], ['reqdel', '移除请求 Cookie']];
var LIFE = { expires: 1, expire: 1, 'max-age': 1, maxage: 1, expiry: 1, lifetime: 1 };
var FLAGS = { secure: 'Secure', httponly: 'HttpOnly', partitioned: 'Partitioned' };
var FALSY = /^(false|0|off|no|关|否|关闭|删除|去掉|remove)$/i;
var INTERVALS = [6, 12, 24, 48, 72, 168];
var PRESETS = [
  ['有效期', { where: 'resp', name: 'expires', value: '20', unit: 'd', mode: 'force', only: '' }, 'value'],
  ['SameSite', { where: 'resp', name: 'SameSite', value: 'Lax', unit: 'd', mode: 'force', only: '' }, 'value'],
  ['拦截 Cookie', { where: 'block', name: '', value: '', unit: 'd', mode: 'force', only: '' }, 'name'],
  ['请求 Cookie', { where: 'req', name: '', value: '', unit: 'd', mode: 'force', only: '' }, 'name'],
  ['移除请求 Cookie', { where: 'reqdel', name: '', value: '', unit: 'd', mode: 'force', only: '' }, 'name']
];

var ICON = {
  chev: '<svg viewBox="0 0 20 20"><path d="M5 7.5l5 5 5-5" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>',
  x: '<svg viewBox="0 0 20 20"><path d="M6 6l8 8M14 6l-8 8" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/></svg>',
  plus: '<svg viewBox="0 0 20 20"><path d="M10 4.5v11M4.5 10h11" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/></svg>',
  up: '<svg viewBox="0 0 20 20"><path d="M10 15.5v-11M5.5 9L10 4.5 14.5 9" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>',
  down: '<svg viewBox="0 0 20 20"><path d="M10 4.5v11M5.5 11l4.5 4.5 4.5-4.5" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>',
  refresh: '<svg viewBox="0 0 20 20"><path d="M15.5 8.5A5.8 5.8 0 0 0 5 6.2M4.5 11.5A5.8 5.8 0 0 0 15 13.8M5 2.8v3.6h3.6M15 17.2v-3.6h-3.6" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"/></svg>',
  copy: '<svg viewBox="0 0 20 20"><rect x="7" y="7" width="9" height="9.5" rx="2" fill="none" stroke="currentColor" stroke-width="1.7"/><path d="M13 4.5A1.5 1.5 0 0 0 11.5 3H5.5A1.5 1.5 0 0 0 4 4.5v7A1.5 1.5 0 0 0 5.5 13" fill="none" stroke="currentColor" stroke-width="1.7"/></svg>'
};
var MARK = '<svg viewBox="0 0 48 48" aria-hidden="true"><defs><mask id="bite"><rect width="48" height="48" fill="#fff"/><circle cx="41" cy="9" r="8.5" fill="#000"/><circle cx="45.5" cy="19.5" r="5" fill="#000"/></mask></defs>' +
  '<circle class="mk-body" cx="23.5" cy="25" r="20" mask="url(#bite)"/>' +
  '<circle class="mk-chip" cx="15.5" cy="19" r="2.7"/><circle class="mk-chip" cx="26" cy="30.5" r="2.7"/>' +
  '<circle class="mk-chip" cx="14.5" cy="32" r="2"/><circle class="mk-chip" cx="28" cy="17.5" r="1.8"/><circle class="mk-chip" cx="34" cy="31" r="1.5"/></svg>';

/* ---------- DOM 工具 ---------- */
function $(id) { return document.getElementById(id); }
function append(el, c) {
  if (c == null || c === false) return;
  if (Array.isArray(c)) { c.forEach(function (x) { append(el, x); }); return; }
  el.appendChild(typeof c === 'object' ? c : document.createTextNode(String(c)));
}
function h(tag, props) {
  var el = document.createElement(tag);
  var pendingValue = null;
  if (props) Object.keys(props).forEach(function (k) {
    var v = props[k];
    if (v === undefined || v === null || v === false) return;
    if (k === 'class') el.className = v;
    else if (k.slice(0, 2) === 'on' && typeof v === 'function') el.addEventListener(k.slice(2), v);
    else if (k === 'value') { if (tag === 'select') pendingValue = v; else el.value = v; }
    else if (k === 'checked' || k === 'disabled' || k === 'readOnly') el[k] = !!v;
    else if (k === 'html') el.innerHTML = v;
    else el.setAttribute(k, v === true ? '' : String(v));
  });
  for (var i = 2; i < arguments.length; i++) append(el, arguments[i]);
  if (pendingValue !== null) el.value = pendingValue;
  return el;
}
function icon(name) { return h('span', { class: 'ic' + (name === 'chev' ? ' chev' : ''), 'aria-hidden': 'true', html: ICON[name] }); }
function spinner() { return h('span', { class: 'spin', 'aria-hidden': 'true' }); }
function busyIs(k) { return S.busy === k; }
function clone(o) { return JSON.parse(JSON.stringify(o)); }
function newId() { return 'r' + Date.now().toString(36) + Math.floor(Math.random() * 1679616).toString(36); }
function lower(s) { return String(s || '').trim().toLowerCase(); }

function fmtInt(n) { return String(Math.round(Number(n) || 0)).replace(/\B(?=(\d{3})+(?!\d))/g, ','); }
function fmtNum(n) { return String(Math.round(Number(n) * 100) / 100); }
function ago(t) {
  if (!t) return '从未';
  var s = Math.max(0, (Date.now() - t) / 1000);
  if (s < 60) return '刚刚';
  if (s < 3600) return Math.floor(s / 60) + ' 分钟前';
  if (s < 86400) return Math.floor(s / 3600) + ' 小时前';
  return Math.floor(s / 86400) + ' 天前';
}
function ymd() {
  var d = new Date();
  function p(n) { return (n < 10 ? '0' : '') + n; }
  return d.getFullYear() + p(d.getMonth() + 1) + p(d.getDate());
}
function shortURL(u) {
  var m = /^https?:\/\/([^\/]+)(\/.*)?$/i.exec(u);
  if (!m || u.length <= 64) return u;
  var segs = (m[2] || '').split('/').filter(Boolean);
  return m[1] + '/…/' + segs.slice(-2).join('/');
}

/* ---------- 接口 ---------- */
function api(method, path, body) {
  var ctl = typeof AbortController === 'function' ? new AbortController() : null;
  var timer = setTimeout(function () { if (ctl) ctl.abort(); }, 90000);
  var opt = { method: method, headers: { 'X-CookieCtl': '1' }, cache: 'no-store', credentials: 'same-origin' };
  if (ctl) opt.signal = ctl.signal;
  if (body !== undefined) { opt.headers['Content-Type'] = 'application/json'; opt.body = JSON.stringify(body); }
  return fetch(path, opt).then(function (r) {
    return r.text().then(function (t) {
      var j = null;
      try { j = JSON.parse(t); } catch (e) { j = null; }
      if (!r.ok || !j) throw new Error((j && j.error) || ('请求失败（HTTP ' + r.status + '）'));
      return j;
    });
  }, function (e) {
    throw new Error(e && e.name === 'AbortError' ? '请求超时，请稍后重试' : '连不上 Surge，请确认 Cookie 管控台模块已启用');
  }).then(function (j) { clearTimeout(timer); return j; }, function (e) { clearTimeout(timer); throw e; });
}

/* ---------- 状态 ---------- */
function applyServer(st) {
  S.srv = st;
  S.base = JSON.stringify(st.cfg);
  S.draft = JSON.parse(S.base);
  render();
}
function isDirty() { return !!S.draft && JSON.stringify(S.draft) !== S.base; }
function touched() { renderSaveBar(); }
function setBusy(k) { S.busy = k; render(); }
function ruleInfo(id) {
  var list = (S.srv && S.srv.rules) || [];
  for (var i = 0; i < list.length; i++) if (list[i].id === id) return list[i];
  return null;
}
function savedRule(id) {
  var list = (S.srv && S.srv.cfg.rules) || [];
  for (var i = 0; i < list.length; i++) if (list[i].id === id) return list[i];
  return null;
}

/* ---------- 参数描述 ---------- */
function isLife(p) { return p.where === 'resp' && LIFE[lower(p.name)] === 1; }
function describe(p) {
  var name = String(p.name || '').trim();
  var v = String(p.value || '').trim();
  var lc = name.toLowerCase();
  var target = p.only && p.only.trim() ? '名称匹配 ' + p.only.trim() + ' 的 Cookie' : '所有 Cookie';
  switch (p.where) {
    case 'resp':
      if (!name) return '填写要改写的属性名，例如 expires。';
      if (LIFE[lc]) {
        var n = Number(v);
        if (v === '' || !isFinite(n) || n < 0) return '有效期需要填一个不小于 0 的数字。';
        if (n === 0) return p.mode === 'cap' ? target + ' 一写入就会过期。' : '网站写入的' + target + ' 会被立即删除。';
        var span = fmtNum(n) + ' ' + UNIT[p.unit || 'd'];
        return p.mode === 'cap'
          ? target + ' 的有效期最长 ' + span + '，本来就更短的保持不变。'
          : target + ' 的有效期统一改为 ' + span + '。';
      }
      if (FLAGS[lc]) return FALSY.test(v) ? '去掉' + target + ' 的 ' + FLAGS[lc] + ' 标记。' : '给' + target + ' 加上 ' + FLAGS[lc] + ' 标记。';
      if (!v) return '去掉' + target + ' 的 ' + name + ' 属性。';
      return '把' + target + ' 的 ' + name + ' 设为 ' + v + '。' + (lc === 'samesite' && v.toLowerCase() === 'none' ? '浏览器要求同时带 Secure，会自动加上。' : '');
    case 'block':
      return name ? '阻止网站写入名称匹配 ' + name + ' 的 Cookie。' : '填写要拦截的 Cookie 名称，可用 * 通配，多个用逗号分隔。';
    case 'req':
      return name ? '发出的请求带上 ' + name + '=' + v + '，已有同名 Cookie 时覆盖。' : '填写要设置的 Cookie 名称和值。';
    case 'reqdel':
      return name ? '发出的请求里去掉名称匹配 ' + name + ' 的 Cookie。' : '填写要移除的 Cookie 名称，可用 * 通配，多个用逗号分隔。';
  }
  return '';
}
function crumb(p) {
  var name = String(p.name || '').trim() || '?';
  var lc = name.toLowerCase();
  var v = String(p.value || '').trim();
  switch (p.where) {
    case 'resp':
      if (LIFE[lc]) return h('span', { class: 'crumb' }, name, h('b', null, (p.mode === 'cap' ? '≤ ' : '') + (v || '?')), UNIT[p.unit || 'd']);
      if (FLAGS[lc]) return h('span', { class: 'crumb' }, (FALSY.test(v) ? '去掉 ' : '加上 ') + FLAGS[lc]);
      return h('span', { class: 'crumb' }, name, h('b', null, v || '删除'));
    case 'block': return h('span', { class: 'crumb' }, '拦截', h('b', null, name));
    case 'req': return h('span', { class: 'crumb req' }, '请求带上', h('b', null, name + '=' + v));
    case 'reqdel': return h('span', { class: 'crumb req' }, '请求去掉', h('b', null, name));
  }
  return null;
}
function fillCrumbs(el, rule) {
  el.textContent = '';
  if (!rule.params.length) { el.appendChild(h('span', { class: 'crumb none' }, '未设定参数')); return; }
  rule.params.forEach(function (p) { append(el, crumb(p)); });
}

/* ---------- 通用控件 ---------- */
var fid = 0;
function toggle(on, cb, label) {
  var inp = h('input', { type: 'checkbox', role: 'switch', checked: !!on, 'aria-label': label });
  inp.addEventListener('change', function () { cb(inp.checked); });
  return h('label', { class: 'sw' }, inp, h('span'));
}
function selectEl(options, value, onChange, extra) {
  var props = { class: 'inp', value: value };
  if (extra) Object.keys(extra).forEach(function (k) { props[k] = extra[k]; });
  var s = h('select', props, options.map(function (o) { return h('option', { value: o[0] }, o[1]); }));
  s.addEventListener('change', function () { onChange(s.value); });
  return s;
}
function textInput(value, onInput, extra) {
  var props = { class: 'inp', value: value || '', autocapitalize: 'off', autocorrect: 'off', autocomplete: 'off', spellcheck: 'false' };
  if (extra) Object.keys(extra).forEach(function (k) { props[k] = extra[k]; });
  var el = h(extra && extra.rows ? 'textarea' : 'input', props);
  el.addEventListener('input', function () { onInput(el.value); });
  return el;
}
function field(label, control, hint, extra) {
  var id = 'f' + (++fid);
  control.id = id;
  return h('div', { class: 'field' }, h('label', { class: 'lbl', for: id }, label), control, hint ? h('p', { class: 'hint' }, hint) : null, extra || null);
}
function mini(label, control) { return h('label', { class: 'mini' }, h('span', null, label), control); }
function notice(content, kind, extra) { return h('div', { class: 'notice' + (kind ? ' ' + kind : '') }, h('div', null, content), extra || null); }

var toastTimer = null;
function toast(msg, kind) {
  var t = $('toast');
  t.textContent = msg;
  t.className = 'toast show' + (kind && kind !== 'ok' ? ' ' + kind : '');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(function () { t.className = 'toast' + (kind && kind !== 'ok' ? ' ' + kind : ''); }, kind === 'err' ? 4200 : 2600);
}

function copyText(text) {
  function legacy() {
    var ta = h('textarea', { readonly: 'readonly', style: 'position:fixed;top:0;left:0;width:1px;height:1px;opacity:0;font-size:16px' });
    ta.value = text;
    document.body.appendChild(ta);
    ta.focus();
    ta.select();
    try { ta.setSelectionRange(0, text.length); } catch (e) {}
    var ok = false;
    try { ok = document.execCommand('copy'); } catch (e) { ok = false; }
    document.body.removeChild(ta);
    return ok;
  }
  if (navigator.clipboard && window.isSecureContext) {
    return navigator.clipboard.writeText(text).then(function () { return true; }, function () { return legacy(); });
  }
  return Promise.resolve(legacy());
}

/* ---------- 渲染 ---------- */
function render() {
  var app = $('app');
  var y = window.pageYOffset;
  var active = document.activeElement;
  var activeId = active && active.id && app.contains(active) ? active.id : '';
  app.textContent = '';
  fid = 0;
  if (!S.srv) {
    if (S.loadError) {
      app.appendChild(renderBrand());
      app.appendChild(h('div', { class: 'top-notices' }, notice(S.loadError, 'err', h('button', { class: 'btn sm', onclick: load }, '重试'))));
    } else {
      app.appendChild(h('p', { class: 'boot' }, '正在载入…'));
    }
    renderSaveBar();
    return;
  }
  app.appendChild(renderTop());
  var tn = renderTopNotices();
  if (tn) app.appendChild(tn);
  app.appendChild(renderRules());
  app.appendChild(renderModule());
  app.appendChild(renderTest());
  app.appendChild(renderSettings());
  app.appendChild(h('footer', { class: 'foot' }, 'Cookie 管控台 ' + S.srv.version + '。域名列表上次定时检查：' + ago(S.srv.lastRun) + '。'));
  renderSaveBar();
  window.scrollTo(0, y);
  if (activeId && $(activeId)) { try { $(activeId).focus({ preventScroll: true }); } catch (e) {} }
}

function renderBrand() {
  return h('div', { class: 'top' }, h('span', { class: 'mark', html: MARK }), h('h1', { class: 'title' }, 'Cookie 管控台'));
}

function moduleStatus() {
  var m = S.srv.module;
  var seen = S.srv.seen;
  if (m.empty) return null;
  if (seen && seen.sig === m.sig) return { k: 'ok', t: '规则模块已生效' };
  if (seen && seen.sig) return { k: 'warn', t: '规则模块需要更新' };
  return { k: 'idle', t: '未检测到规则模块' };
}

function renderTop() {
  var cfg = S.draft;
  var st = moduleStatus();
  var saved = S.srv.cfg;
  var line;
  if (!saved.enabled) line = '管控已暂停，所有请求都会原样放行。';
  else if (!S.srv.module.rules) line = '还没有生效的规则集。';
  else if (!S.srv.module.domains) line = ['已启用 ', h('b', null, fmtInt(S.srv.module.rules)), ' 个规则集，域名列表还没有下载。'];
  else line = ['正在管控 ', h('b', null, fmtInt(S.srv.module.rules)), ' 个规则集里的 ', h('b', null, fmtInt(S.srv.module.domains)), ' 个域名。'];
  var top = renderBrand();
  top.appendChild(h('span', { class: 'sp' }));
  top.appendChild(toggle(cfg.enabled, function (on) { cfg.enabled = on; touched(); }, '启用 Cookie 管控'));
  return h('header', null, top,
    h('p', { class: 'status' }, line, st && saved.enabled ? [' ', h('a', { class: 'pill ' + st.k, href: '#module' }, h('i'), st.t)] : null));
}

function renderTopNotices() {
  var items = [];
  if (S.srv.indexError) items.push(notice(S.srv.indexError, 'err'));
  if (S.warnings.length) {
    items.push(notice([h('div', null, '保存时有些内容被调整了：'), h('ul', null, S.warnings.map(function (w) { return h('li', null, w); }))], 'warn',
      h('button', { class: 'btn ghost sm', onclick: function () { S.warnings = []; render(); } }, '知道了')));
  }
  return items.length ? h('div', { class: 'top-notices' }, items) : null;
}

/* 规则集 */
function addRule() {
  var r = { id: newId(), name: '新规则集', enabled: true, sources: [], extra: '', params: [clone(PRESETS[0][1])] };
  S.draft.rules.push(r);
  S.open[r.id] = true;
  touched();
  render();
  var el = document.querySelector('#rule-' + r.id + ' textarea');
  if (el) { el.scrollIntoView({ block: 'center' }); el.focus(); }
}
function moveRule(i, d) {
  var list = S.draft.rules;
  var j = i + d;
  if (j < 0 || j >= list.length) return;
  var t = list[i]; list[i] = list[j]; list[j] = t;
  touched();
  render();
}

function renderRules() {
  var list = h('div');
  S.draft.rules.forEach(function (r, i) { list.appendChild(renderRule(r, i)); });
  if (!S.draft.rules.length) {
    list.appendChild(h('div', { class: 'empty' },
      h('p', null, '还没有规则集。新建一个，填入域名列表地址，再设定要改写的 Cookie 参数。'),
      h('button', { class: 'btn primary', onclick: addRule }, icon('plus'), '新建规则集')));
  }
  var hasSources = S.srv.cfg.rules.some(function (r) { return r.sources.length; });
  return h('section', { class: 'sec', id: 'rules' },
    h('div', { class: 'sec-h' }, h('h2', null, '规则集'), h('span', { class: 'sp' }),
      hasSources ? h('button', { class: 'btn ghost sm', disabled: !!S.busy, onclick: function () { refresh(''); } },
        busyIs('refresh:') ? spinner() : icon('refresh'), '全部更新') : null,
      S.draft.rules.length ? h('button', { class: 'btn sm', onclick: addRule }, icon('plus'), '新建规则集') : null),
    list);
}

function ruleMeta(rule, info) {
  if (!info) return { t: '未保存', bad: false };
  var failed = info.sources.filter(function (s) { return !s.ok && s.tried; }).length;
  if (failed) return { t: failed + ' 个列表下载失败', bad: true };
  if (info.count) return { t: fmtInt(info.count) + ' 个域名', bad: false };
  if (!rule.sources.length && !String(rule.extra || '').trim()) return { t: '未填写域名', bad: false };
  return { t: '尚未下载', bad: false };
}

function renderRule(rule, i) {
  var info = ruleInfo(rule.id);
  var open = !!S.open[rule.id];
  var panel = h('article', { class: 'rule' + (rule.enabled ? '' : ' off') + (open ? ' open' : ''), id: 'rule-' + rule.id });
  var ctx = {
    nameEl: h('span', { class: 'rule-name' }, rule.name || '未命名'),
    crumbsEl: h('div', { class: 'crumbs' }),
    redraw: function (focusSel) {
      var np = renderRule(rule, i);
      panel.replaceWith(np);
      panel = np;
      if (focusSel) {
        var el = np.querySelector(focusSel);
        if (el) {
          el.focus();
          try { if (el.setSelectionRange && typeof el.value === 'string') el.setSelectionRange(el.value.length, el.value.length); } catch (e) {}
        }
      }
    }
  };
  ctx.fill = function () { fillCrumbs(ctx.crumbsEl, rule); };
  ctx.fill();
  var meta = ruleMeta(rule, info);
  panel.appendChild(h('div', { class: 'rule-head' },
    toggle(rule.enabled, function (on) { rule.enabled = on; panel.classList.toggle('off', !on); touched(); }, '启用规则集'),
    h('button', { class: 'rule-tap', 'aria-expanded': open ? 'true' : 'false', onclick: function () { S.open[rule.id] = !open; ctx.redraw(); } },
      h('span', { class: 'rule-title' }, ctx.nameEl, h('span', { class: 'rule-meta' + (meta.bad ? ' bad' : '') }, meta.t)), icon('chev'))));
  panel.appendChild(ctx.crumbsEl);
  if (open) panel.appendChild(renderRuleBody(rule, i, info, ctx));
  return panel;
}

function renderSources(rule, info) {
  if (!rule.sources.length) return null;
  var map = {};
  (info ? info.sources : []).forEach(function (s) { map[s.url] = s; });
  return h('ul', { class: 'srcs' }, rule.sources.map(function (u) {
    var s = map[u];
    var dot, txt;
    if (!s) { dot = 'wait'; txt = '保存后自动下载'; }
    else if (s.ok) { dot = 'ok'; txt = fmtInt(s.n) + ' 条域名规则，' + ago(s.at) + '更新' + (s.skipped ? '，忽略了 ' + fmtInt(s.skipped) + ' 条其它规则' : '') + '。'; }
    else if (s.at) { dot = 'bad'; txt = '最近一次更新失败：' + s.err + '。正在使用' + ago(s.at) + '下载的版本。'; }
    else if (s.tried) { dot = 'bad'; txt = '下载失败：' + s.err + '。'; }
    else { dot = 'wait'; txt = '尚未下载。'; }
    return h('li', { class: 'src' }, h('i', { class: 'dot ' + dot }), h('div', null, h('div', { class: 'src-url' }, shortURL(u)), h('div', null, txt)));
  }));
}

function renderRuleBody(rule, i, info, ctx) {
  var body = h('div', { class: 'rule-body' });

  body.appendChild(field('名称', textInput(rule.name, function (v) {
    rule.name = v;
    ctx.nameEl.textContent = v || '未命名';
    touched();
  }, { maxlength: 40, autocapitalize: 'sentences' })));

  var sourcesEl = textInput(rule.sources.join('\n'), function (v) {
    rule.sources = v.split(/\r?\n/).map(function (s) { return s.trim(); }).filter(Boolean);
    touched();
  }, { rows: 3, placeholder: 'https://raw.githubusercontent.com/…/Baidu.list', inputmode: 'url' });
  var upd = rule.sources.length ? h('div', { class: 'row-actions' },
    h('button', { class: 'btn sm', disabled: !!S.busy, onclick: function () { refresh(rule.id); } },
      busyIs('refresh:' + rule.id) ? spinner() : icon('refresh'), '更新这个规则集')) : null;
  body.appendChild(field('域名列表地址', sourcesEl,
    '每行一个地址。支持 Surge、Clash、Quantumult X 格式的规则列表，只读取 DOMAIN、DOMAIN-SUFFIX、DOMAIN-KEYWORD、DOMAIN-WILDCARD 这几类规则。',
    [renderSources(rule, info), upd]));

  body.appendChild(field('补充域名', textInput(rule.extra, function (v) { rule.extra = v; touched(); },
    { rows: 2, placeholder: 'example.com' }),
    '每行一个。直接写域名会连同子域名一起匹配；写成 DOMAIN,api.example.com 则只匹配这一个域名。'));

  body.appendChild(renderParams(rule, ctx));

  body.appendChild(h('div', { class: 'rule-foot' },
    h('button', { class: 'btn ghost sm', disabled: i === 0, onclick: function () { moveRule(i, -1); } }, icon('up'), '上移'),
    h('button', { class: 'btn ghost sm', disabled: i === S.draft.rules.length - 1, onclick: function () { moveRule(i, 1); } }, icon('down'), '下移'),
    h('span', { class: 'sp' }),
    h('button', { class: 'btn danger sm', onclick: function () {
      if (!confirm('删除规则集「' + (rule.name || '未命名') + '」？点「保存并应用」后生效。')) return;
      S.draft.rules.splice(i, 1);
      delete S.open[rule.id];
      touched();
      render();
    } }, '删除规则集')));
  return body;
}

function renderParams(rule, ctx) {
  var list = h('div', { class: 'params' });
  rule.params.forEach(function (p, j) { list.appendChild(renderParam(rule, p, j, ctx)); });
  if (!rule.params.length) list.appendChild(h('p', { class: 'hint' }, '还没有参数。没有参数的规则集不会改动任何 Cookie。'));
  return h('div', { class: 'field' },
    h('div', { class: 'lbl' }, 'Cookie 参数'),
    h('p', { class: 'hint', style: 'margin:-3px 0 10px' }, '同一个规则集里按从上到下的顺序执行；多个规则集命中同一个域名时，排在后面的规则集会覆盖前面的设定。'),
    list,
    h('div', { class: 'quick' }, PRESETS.map(function (pr) {
      return h('button', { class: 'btn sm dashed', onclick: function () {
        rule.params.push(clone(pr[1]));
        touched();
        ctx.redraw('.param:last-child [data-k="' + pr[2] + '"]');
      } }, icon('plus'), pr[0]);
    })));
}

function renderParam(rule, p, j, ctx) {
  var box = h('div', { class: 'param' });
  var descEl = h('p', { class: 'param-desc' }, describe(p));
  var sel = function (k) { return '.params > .param:nth-child(' + (j + 1) + ') [data-k="' + k + '"]'; };
  function changed() { ctx.fill(); descEl.textContent = describe(p); touched(); }

  box.appendChild(h('div', { class: 'param-top' },
    selectEl(WHERE, p.where, function (v) { p.where = v; touched(); ctx.redraw(sel('where')); }, { 'data-k': 'where', 'aria-label': '作用位置' }),
    h('button', { class: 'icon-btn', 'aria-label': '删除这个参数', title: '删除这个参数', onclick: function () {
      rule.params.splice(j, 1);
      touched();
      ctx.redraw();
    } }, icon('x'))));

  var namePh = { resp: 'expires', block: '例如 _ga*', req: '例如 lang', reqdel: '例如 tracking_id' }[p.where];
  var nameEl = textInput(p.name, function (v) {
    var was = isLife(p);
    p.name = v;
    if (isLife(p) !== was) { touched(); ctx.redraw(sel('name')); } else changed();
  }, { 'data-k': 'name', placeholder: namePh, list: p.where === 'resp' ? 'attr-names' : null, maxlength: 64 });

  var lc = lower(p.name);
  var valPh = isLife(p) ? '20' : lc === 'samesite' ? 'Lax、Strict 或 None' : FLAGS[lc] ? 'true 或 false' : '参数值';
  var valEl = textInput(p.value, function (v) { p.value = v; changed(); },
    { 'data-k': 'value', placeholder: valPh, inputmode: isLife(p) ? 'decimal' : null, maxlength: 512 });

  if (p.where === 'resp' || p.where === 'req') {
    if (isLife(p)) {
      box.appendChild(h('div', { class: 'param-grid life' },
        mini('参数名', nameEl), mini('参数值', valEl),
        mini('单位', selectEl([['s', '秒'], ['m', '分钟'], ['h', '小时'], ['d', '天']], p.unit || 'd', function (v) { p.unit = v; changed(); }, { 'data-k': 'unit' })),
        mini('方式', selectEl([['force', '强制设为'], ['cap', '最长不超过']], p.mode || 'force', function (v) { p.mode = v; changed(); }, { 'data-k': 'mode' }))));
    } else {
      box.appendChild(h('div', { class: 'param-grid' },
        mini(p.where === 'req' ? 'Cookie 名称' : '参数名', nameEl), mini('参数值', valEl)));
    }
  } else {
    box.appendChild(h('div', { class: 'param-grid one' }, mini('Cookie 名称', nameEl)));
  }

  if (p.where === 'resp') {
    box.appendChild(h('div', { class: 'param-grid one' }, mini('仅作用于这些 Cookie（可选）',
      textInput(p.only, function (v) { p.only = v; changed(); }, { 'data-k': 'only', placeholder: '留空表示全部，例如 sid, token*', maxlength: 256 }))));
  }
  box.appendChild(descEl);
  return box;
}

/* 规则模块 */
function renderModule() {
  var m = S.srv.module;
  var st = moduleStatus();
  var panel = h('div', { class: 'panel' });
  if (isDirty()) panel.appendChild(notice('有未保存的修改，保存后模块内容才会更新。', 'warn'));
  if (m.empty) {
    panel.appendChild(h('p', { style: 'margin:0;color:var(--ink-2)' }, '目前没有需要处理的域名。启用至少一个规则集，填好域名列表和 Cookie 参数并保存后，这里会生成模块内容。'));
  } else {
    var tip = st.k === 'ok' ? '最近一次运行于' + ago(S.srv.seen.at) + '。'
      : st.k === 'warn' ? '已安装的是旧版本，把下面的新内容替换进去。'
      : '安装后访问一次受控网站，这里会显示已生效。';
    panel.appendChild(h('div', { class: 'mod-status' }, h('span', { class: 'pill ' + st.k }, h('i'), st.t),
      h('span', { class: 'mod-facts' }, '覆盖 ' + fmtInt(m.domains) + ' 个域名，HTTPS 解密 ' + fmtInt(m.hosts) + ' 个主机名。')));
    panel.appendChild(h('p', { class: 'hint', style: 'margin-top:2px' }, tip));
    panel.appendChild(h('ol', { class: 'steps' },
      h('li', null, '复制下面的模块内容。'),
      h('li', null, '在 Surge 的「模块」里新建本地模块，例如命名为 CookieCtl-Rules，粘贴后保存。已经建过的，打开它全选替换即可。'),
      h('li', null, '启用这个模块，并确认 HTTPS 解密（MITM）已开启、证书已安装并信任。')));
    panel.appendChild(h('div', { class: 'actions' },
      h('button', { class: 'btn primary', onclick: function () {
        copyText(m.text).then(function (ok) {
          if (ok) toast('已复制模块内容', 'ok');
          else { S.showModule = true; render(); toast('无法自动复制，请在下方手动全选复制', 'warn'); }
        });
      } }, icon('copy'), '复制模块'),
      h('button', { class: 'btn', onclick: function () { S.showModule = !S.showModule; render(); } }, S.showModule ? '收起内容' : '查看内容'),
      h('a', { class: 'btn ghost', href: '/rules.sgmodule', target: '_blank', rel: 'noopener' }, '在新页面打开')));
    if (S.showModule) panel.appendChild(h('pre', { class: 'code' }, m.text));
  }
  return h('section', { class: 'sec', id: 'module' },
    h('div', { class: 'sec-h' }, h('h2', null, '规则模块')),
    h('p', { class: 'sec-note' }, 'Surge 的模块装好后内容是固定的，所以受控域名的脚本匹配和 HTTPS 解密主机名放在一个单独的模块里。域名列表或参数变化后，回到这里重新复制。'),
    panel);
}

/* 测试 */
function runTest() {
  var v = String(S.testInput || '').trim();
  if (!v) { toast('请输入要测试的网址', 'warn'); return; }
  setBusy('test');
  api('POST', '/api/test', { url: v }).then(function (j) { S.test = j; }, function (e) { S.test = { error: e.message }; })
    .then(function () { setBusy(''); });
}

function renderTest() {
  var inp = textInput(S.testInput, function (v) { S.testInput = v; }, { type: 'url', inputmode: 'url', placeholder: 'https://www.baidu.com', 'aria-label': '要测试的网址', id: 'test-url' });
  inp.addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); runTest(); } });
  return h('section', { class: 'sec', id: 'test' },
    h('div', { class: 'sec-h' }, h('h2', null, '测试网址')),
    h('p', { class: 'sec-note' }, '按已保存的配置，看看某个网址的 Cookie 会被怎样处理。'),
    h('div', { class: 'test-row' }, inp,
      h('button', { class: 'btn primary', disabled: !!S.busy, onclick: runTest }, busyIs('test') ? spinner() : null, '测试')),
    S.test ? renderTestResult(S.test) : null);
}

function renderTestResult(r) {
  if (r.error) return h('div', { class: 'result' }, notice(r.error, 'err'));
  var box = h('div', { class: 'result' });
  if (!r.rules.length) {
    box.appendChild(h('p', null, h('span', { class: 'mono' }, r.host), ' 不在任何生效的规则集里，Cookie 不会被改动。'));
    return box;
  }
  box.appendChild(h('p', null, h('span', { class: 'mono' }, r.host), ' 命中 ' + r.rules.length + ' 个规则集：'));
  r.rules.forEach(function (rr) {
    var rule = savedRule(rr.id);
    box.appendChild(h('div', { class: 'hit' },
      h('div', { class: 'hit-h' }, h('b', null, rr.name), h('span', { class: 'hit-via' }, '匹配' + rr.via)),
      h('ul', null, (rule ? rule.params : []).map(function (p) { return h('li', null, describe(p)); }))));
  });
  var checks = [];
  if (!r.enabled) checks.push(['bad', '管控总开关已关闭，目前不会改动任何 Cookie。']);
  checks.push(r.covered ? ['ok', '规则模块包含这个地址。'] : ['bad', '规则模块还没包含这个地址，保存后重新复制规则模块。']);
  if (r.https) checks.push(r.mitm ? ['ok', 'HTTPS 解密列表包含这个主机名。'] : ['bad', 'HTTPS 解密列表不含这个主机名，可能在「HTTPS 解密排除」里。']);
  if (!r.moduleCurrent) checks.push(['wait', '尚未确认已安装的规则模块是最新版本。']);
  box.appendChild(h('div', { class: 'checks' }, checks.map(function (c) {
    return h('div', { class: 'check' }, h('i', { class: 'dot ' + c[0] }), h('span', null, c[1]));
  })));
  return box;
}

/* 设置 */
function row(title, desc, control, col) {
  return h('div', { class: 'row' + (col ? ' col' : '') }, h('div', { class: 'k' }, h('div', null, title), desc ? h('small', null, desc) : null), control);
}

function renderSettings() {
  var c = S.draft;
  var fileInp = h('input', { type: 'file', accept: '.json,application/json', class: 'file-hidden', tabindex: '-1', 'aria-hidden': 'true' });
  fileInp.addEventListener('change', function () { if (fileInp.files && fileInp.files[0]) importFile(fileInp.files[0]); fileInp.value = ''; });

  var g1 = h('div', { class: 'group' },
    row('自动更新', '定时重新下载域名列表',
      selectEl(INTERVALS.map(function (n) {
        return [String(n), n < 24 ? '每 ' + n + ' 小时' : n === 24 ? '每天' : n === 168 ? '每周' : '每 ' + (n / 24) + ' 天'];
      }), String(c.interval), function (v) { c.interval = Number(v); touched(); }, { 'aria-label': '自动更新间隔' })),
    row('下载使用的策略', '留空则按规则分流。直连 GitHub 较慢时，可以填一个代理策略或策略组的名称。',
      textInput(c.policy, function (v) { c.policy = v; touched(); }, { placeholder: '例如 Proxy', 'aria-label': '下载使用的策略', maxlength: 64 })),
    row('更新失败时通知', '域名列表下载失败，或列表变化需要重新复制规则模块时提醒',
      toggle(c.notify, function (on) { c.notify = on; touched(); }, '更新失败时通知')),
    row('调试日志', '在 Surge 的脚本日志里记录每次改写',
      toggle(c.debug, function (on) { c.debug = on; touched(); }, '调试日志')),
    row('HTTPS 解密排除', '这些主机名不会被解密。某个 App 因证书校验而无法联网时，把它的域名加在这里。每行一个，支持 * 通配。',
      textInput(c.mitmExclude, function (v) { c.mitmExclude = v; touched(); }, { rows: 2, placeholder: 'pan.baidu.com', 'aria-label': 'HTTPS 解密排除' }), true),
    row('脚本路径', '规则模块引用的脚本位置，要和主模块里的 script-path 一致。留空时使用 ' + S.srv.defaultScriptPath + '。',
      textInput(c.scriptPath, function (v) { c.scriptPath = v; touched(); }, { placeholder: S.srv.defaultScriptPath, 'aria-label': '脚本路径', maxlength: 512 }), true));

  var g2 = h('div', { class: 'group' },
    row('导出配置', '下载一份 JSON 备份', h('button', { class: 'btn sm', onclick: exportConfig }, '导出')),
    row('导入配置', '从备份文件恢复，导入后需要保存', h('span', null, fileInp, h('button', { class: 'btn sm', onclick: function () { fileInp.click(); } }, '导入'))),
    row('恢复默认', '清空所有规则集和设置，回到初始示例',
      h('button', { class: 'btn danger sm', disabled: !!S.busy, onclick: resetAll }, busyIs('reset') ? spinner() : null, '恢复默认')));

  return h('section', { class: 'sec', id: 'settings' }, h('div', { class: 'sec-h' }, h('h2', null, '设置')), g1, g2);
}

function renderSaveBar() {
  var bar = $('savebar');
  var dirty = isDirty();
  var key = (dirty ? '1' : '0') + '|' + S.busy;
  if (key === S.barState) return;
  S.barState = key;
  bar.className = 'savebar' + (dirty ? ' show' : '');
  bar.setAttribute('aria-hidden', dirty ? 'false' : 'true');
  bar.textContent = '';
  bar.appendChild(h('span', { class: 'msg' }, '有未保存的修改'));
  bar.appendChild(h('button', { class: 'btn ghost', disabled: !!S.busy, onclick: discard }, '撤销'));
  bar.appendChild(h('button', { class: 'btn primary', disabled: !!S.busy, onclick: save }, busyIs('save') ? spinner() : null, '保存并应用'));
}

/* ---------- 动作 ---------- */
function load() {
  S.loadError = '';
  render();
  api('GET', '/api/state').then(function (st) {
    applyServer(st);
    /* 首次打开时，自动下载还从未尝试过的列表 */
    var pending = st.cfg.rules.some(function (r) {
      var info = ruleInfo(r.id);
      return r.enabled && info && info.sources.some(function (s) { return !s.tried; });
    });
    if (pending) refresh('');
  }, function (e) { S.loadError = e.message; render(); });
}

function discard() {
  S.draft = JSON.parse(S.base);
  render();
  toast('已撤销未保存的修改', 'ok');
}

function reportText(rep, okText) {
  rep = rep || {};
  if (rep.timeout) return ['部分列表还在下载，稍后会由定时任务补上', 'warn'];
  if (rep.failed && rep.failed.length) return [rep.failed.length + ' 个域名列表下载失败，详情见规则集', 'warn'];
  return [okText, 'ok'];
}

function save() {
  if (S.busy) return Promise.resolve(false);
  setBusy('save');
  return api('POST', '/api/config', { config: S.draft }).then(function (j) {
    S.warnings = j.state.warnings || [];
    S.busy = '';
    applyServer(j.state);
    var r = reportText(j.report, S.warnings.length ? '已保存，有内容被调整' : '已保存');
    toast(r[0], S.warnings.length ? 'warn' : r[1]);
    return true;
  }, function (e) {
    setBusy('');
    toast(e.message, 'err');
    return false;
  });
}

function refresh(id) {
  function go() {
    setBusy('refresh:' + id);
    return api('POST', '/api/refresh', { rule: id }).then(function (j) {
      S.busy = '';
      applyServer(j.state);
      var n = (j.report && j.report.ok) || 0;
      var r = reportText(j.report, n ? '已更新 ' + n + ' 个域名列表' : '没有需要更新的列表');
      toast(r[0], r[1]);
    }, function (e) { setBusy(''); toast(e.message, 'err'); });
  }
  if (isDirty()) return save().then(function (ok) { if (ok) return go(); });
  return go();
}

function resetAll() {
  if (!confirm('恢复默认会清空所有规则集和设置，确定继续？')) return;
  setBusy('reset');
  api('POST', '/api/reset', {}).then(function (j) {
    S.open = {};
    S.warnings = [];
    S.test = null;
    S.busy = '';
    applyServer(j.state);
    toast('已恢复默认', 'ok');
  }, function (e) { setBusy(''); toast(e.message, 'err'); });
}

function exportConfig() {
  var data = JSON.stringify({ app: 'CookieCtl', version: S.srv.version, exportedAt: new Date().toISOString(), config: S.srv.cfg }, null, 2);
  var url = URL.createObjectURL(new Blob([data], { type: 'application/json' }));
  var a = h('a', { href: url, download: 'cookiectl-' + ymd() + '.json', style: 'display:none' });
  document.body.appendChild(a);
  a.click();
  setTimeout(function () { URL.revokeObjectURL(url); a.remove(); }, 1500);
  toast(isDirty() ? '已导出（不含未保存的修改）' : '已导出', 'ok');
}

function importFile(file) {
  var rd = new FileReader();
  rd.onload = function () {
    try {
      var obj = JSON.parse(String(rd.result || ''));
      var cfg = obj && obj.config && typeof obj.config === 'object' ? obj.config : obj;
      if (!cfg || typeof cfg !== 'object' || !Array.isArray(cfg.rules)) throw new Error('bad');
      var d = clone(S.draft);
      ['enabled', 'interval', 'policy', 'mitmExclude', 'notify', 'debug', 'scriptPath'].forEach(function (k) { if (k in cfg) d[k] = cfg[k]; });
      d.rules = cfg.rules.filter(function (r) { return r && typeof r === 'object'; }).map(function (r) {
        return {
          id: typeof r.id === 'string' && /^[a-z0-9]{1,24}$/.test(r.id) ? r.id : newId(),
          name: String(r.name || ''),
          enabled: r.enabled !== false,
          sources: Array.isArray(r.sources) ? r.sources.map(String) : [],
          extra: String(r.extra || ''),
          params: (Array.isArray(r.params) ? r.params : []).filter(function (p) { return p && typeof p === 'object'; }).map(function (p) {
            return { where: String(p.where || 'resp'), name: String(p.name || ''), value: p.value == null ? '' : String(p.value),
              unit: String(p.unit || 'd'), mode: p.mode === 'cap' ? 'cap' : 'force', only: String(p.only || '') };
          })
        };
      });
      S.draft = d;
      render();
      toast('已导入 ' + d.rules.length + ' 个规则集，检查后点「保存并应用」', 'ok');
    } catch (e) {
      toast('这个文件不是有效的 Cookie 管控台配置', 'err');
    }
  };
  rd.onerror = function () { toast('读取文件失败', 'err'); };
  rd.readAsText(file);
}

window.addEventListener('beforeunload', function (e) {
  if (isDirty()) { e.preventDefault(); e.returnValue = ''; }
});
document.addEventListener('visibilitychange', function () {
  if (document.hidden || !S.srv || S.busy || isDirty()) return;
  api('GET', '/api/state').then(function (st) { if (!S.busy && !isDirty()) applyServer(st); }, function () {});
});

load();
})();
</script>
</body>
</html>
`;
}
