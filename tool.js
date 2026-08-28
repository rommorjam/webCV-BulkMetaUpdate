/**
 * ============================================================================
 * CVホイミン
 * Version 1.0.19
 * ============================================================================
 * targetCode.js v5 の更新エンジンをベースに、ブックマークレット配布用のUIを追加。
 *
 * 主要仕様:
 * - 素材検索画面（元素材・OA素材）/ コンテナ画面のサムネイル表示・リスト表示に対応
 * - 素材検索は元素材のみ / OA素材のみ / 両方の検索結果を処理可能
 * - 素材の存在検知を番号書式から分離し、素材番号は専用DOMから緩く取得・正規化
 * - 2画面モードでは実行不可
 * - 「CV収録送出」グループ選択時のみ実行
 * - 削除日+預入日 / 削除日のみの2モード（左側の削除日+預入日を起動時デフォルト選択）
 * - 削除日は既存値以上の場合のみ処理（前倒し禁止・既存値空欄は素材全体をスキップ）
 * - Error を最優先で除外し、素材タイトル空は全画面・全素材で事前スキップ
 * - サムネイル枠src空 + 素材タイトル空は、ユーザー表示上「削除済み」としてスキップ
 * - Not Filed サムネイルでも素材タイトル有 + Errorなしなら通常素材と同じ処理対象
 * - リスト表示では「素材タイトル」列の表示を必須とし、列が無ければ実行しない
 * - リスト表示では一覧の「削除日」「預入日」を任意取得し、ツール一覧の初期日付として表示（列なし/空欄は—、実行可否には影響しない）
 * - ツール一覧の「削除日」「預入日」は常に最後に確認できた実日付を表示し、処理内容は「結果 / 状態」「詳細」に集約
 * - 起動時の削除日・預入日は空欄。削除日は常に必須、モード2では預入日も必須
 * - モード2で預入日が空欄なら、削除日選択時またはモード2切替時に削除日前日を自動補完（実行日より前になる場合は補完しない）
 * - 日付入力欄のクリックでもネイティブ日付選択カレンダーを開く（showPicker対応ブラウザ）
 * - 削除日・預入日はツール実行日以降のみ選択可能
 * - 削除日 > 預入日 を必須条件とする
 * - 実行直前に対象スナップショットを再検証し、変化があれば中断
 * - 実行中はwebCV画面操作をガードし、離脱時にブラウザ警告を表示
 * - 対象素材ごとの進捗・結果を同一画面でリアルタイム表示
 * - 一覧左端のチェックボックスで実行対象を選択可能。処理可能素材は初期ON、事前スキップ素材はOFF固定
 * - ヘッダチェックで処理可能素材を全選択/全解除。選択0件では実行不可
 * - 一覧6列はヘッダクリックで昇順→降順→ソートOFF。ソートは表示順だけを変更し、実処理順・orderは不変
 * - ソート時の値なし(null/空文字/-/—)は最小値として扱い、昇順では先頭・降順では末尾
 * - 不可視iframe、Workerタイマー、再描画対策、保存後検証、1回リトライを維持
 * ============================================================================
 */
(function () {
  'use strict';

  var TOOL_VERSION = '1.0.19';
  var TOOL_GLOBAL = '__cvDateBatchTool';
  var RESULT_GLOBAL = '__cvDeleteDateResults';

  // 既に読み込み済みの場合:
  // - 同じ版なら既存インスタンスを再表示
  // - 新版が読み込まれた場合は、実行中でなければ旧版を破棄して新版へ入れ替える
  // これにより同じタブを開き続けていても、次回クリック時に最新版が使われる。
  if (window[TOOL_GLOBAL]) {
    var existingTool = window[TOOL_GLOBAL];
    if (existingTool.version === TOOL_VERSION && typeof existingTool.show === 'function') {
      existingTool.show();
      return;
    }
    if (existingTool.running) {
      if (typeof existingTool.show === 'function') existingTool.show();
      return;
    }
    if (typeof existingTool.destroy === 'function') {
      existingTool.destroy();
    } else {
      var oldHost = document.getElementById('cv-date-batch-tool-host');
      if (oldHost) oldHost.remove();
      try { delete window[TOOL_GLOBAL]; } catch (e) { window[TOOL_GLOBAL] = null; }
    }
  }

  // ===== 調整用パラメータ ====================================================
  var USE_IFRAME = true;            // true: 不可視iframe方式 / false: ポップアップ方式
  var STEP_TIMEOUT_MS = 20000;      // 各ステップ(画面反応待ち)のタイムアウト
  var POLL_MS = 250;                // 状態ポーリング間隔
  var BETWEEN_MATERIALS_MS = 800;   // 素材間の待機(サーバー負荷軽減)
  var MAX_ATTEMPTS = 2;             // 素材ごとの最大試行回数(=1回リトライ)

  var host = null;
  var shadow = null;
  var running = false;
  var currentContext = null;
  var launchSnapshot = null;
  var rowModels = [];
  var rowEls = new Map();
  var worker = null;
  var sleep = null;
  var captured = null;
  var originalWindowOpen = null;
  var guardCleanup = null;
  var beforeUnloadHandler = null;
  var executionDateIso = null;
  var sortState = { key: null, direction: null };
  var sortCollator = null;
  try {
    if (typeof Intl !== 'undefined' && typeof Intl.Collator === 'function') {
      sortCollator = new Intl.Collator(['ja', 'en'], { numeric: true, sensitivity: 'base' });
    }
  } catch (e) {
    // Intl.Collatorが利用できない環境ではlocaleCompareへフォールバックする。
    sortCollator = null;
  }

  // ===== 共通ユーティリティ ==================================================
  function visible(el) {
    return !!el && el.getBoundingClientRect().width > 0;
  }

  // 素材番号は将来の採番体系変更に耐えるため、意味的な採番規則は検証しない。
  // DOM上の「素材番号専用位置」から取得した値だけを対象に、
  // 表示用ハイフン/空白を除去・大文字化した半角英数字6〜20文字を内部キーとする。
  var MATERIAL_NO_MIN_LEN = 6;
  var MATERIAL_NO_MAX_LEN = 20;

  function normalizeMaterialNo(raw) {
    if (raw == null) return null;
    var display = String(raw).trim().replace(/\s+/g, '').toUpperCase();
    if (!display) return null;
    var key = display.replace(/-/g, '');
    if (key.length < MATERIAL_NO_MIN_LEN || key.length > MATERIAL_NO_MAX_LEN) return null;
    if (!/^[A-Z0-9]+$/.test(key)) return null;
    return { key: key, display: display, raw: String(raw).trim() };
  }

  function uniqueMaterialCandidates(candidates) {
    var byKey = new Map();
    candidates.forEach(function (c) {
      if (c && c.key && !byKey.has(c.key)) byKey.set(c.key, c);
    });
    return Array.from(byKey.values());
  }

  function getMaterialNoFromAnchor(scope) {
    if (!scope) return { value: null, reason: '素材番号DOMを取得できない' };
    var candidates = [];
    Array.from(scope.querySelectorAll('span.h6')).forEach(function (h6) {
      var parent = h6.parentElement;
      if (!parent) return;
      var prefix = Array.from(parent.childNodes)
        .filter(function (n) { return n.nodeType === 3; })
        .map(function (n) { return (n.textContent || '').trim(); })
        .join('');
      var raw = prefix + (h6.textContent || '').trim();
      var normalized = normalizeMaterialNo(raw);
      if (normalized) candidates.push(normalized);
    });
    candidates = uniqueMaterialCandidates(candidates);
    if (candidates.length === 1) return { value: candidates[0], source: 'span.h6' };
    if (candidates.length > 1) return { value: null, reason: '素材番号候補が複数見つかった' };
    return { value: null, reason: '素材番号専用DOMから有効な番号を取得できない' };
  }

  function getMaterialNoFromListHeader(row) {
    if (!row || !row.closest) return { value: null, reason: '素材番号列を特定できない' };
    var table = row.closest('table.search-list');
    if (!table) return { value: null, reason: '素材番号列を特定できない' };
    var headers = Array.from(table.querySelectorAll('thead th, thead td')).filter(function (cell) {
      return (cell.innerText || cell.textContent || '').trim() === '素材番号';
    });
    if (headers.length !== 1) {
      return { value: null, reason: headers.length > 1 ? '素材番号列が複数見つかった' : '素材番号列を特定できない' };
    }
    var index = headers[0].cellIndex;
    var cell = row.cells && row.cells[index];
    if (!cell) return { value: null, reason: '素材番号セルを取得できない' };
    var normalized = normalizeMaterialNo((cell.textContent || '').trim());
    return normalized ? { value: normalized, source: 'header-column' }
      : { value: null, reason: '素材番号セルの値を正規化できない' };
  }

  function getMaterialNo(scope, viewMode) {
    var anchored = getMaterialNoFromAnchor(scope);
    if (anchored.value) return anchored;
    if (viewMode === 'list') {
      var fallback = getMaterialNoFromListHeader(scope);
      if (fallback.value) return fallback;
      return { value: null, reason: anchored.reason + ' / ' + fallback.reason };
    }
    return anchored;
  }

  function findPreviewTrigger(scope, viewMode) {
    if (!scope) return null;
    var photo = scope.querySelector('img.photo');
    if (photo) return photo;
    var thumbnailImage = Array.from(scope.querySelectorAll('img')).find(function (img) {
      var src = String(img.getAttribute('src') || '');
      return /\/Thumbnail\//i.test(src) && !/ThumbnailMark/i.test(src);
    });
    if (thumbnailImage) return thumbnailImage;
    if (viewMode === 'list') return null;
    return scope.querySelector('img') || scope;
  }

  // タイトル空・白サムネイル判定は、既存のプレビュー起動要素取得とは分離する。
  // カット素材由来ではハサミアイコンにも photo クラスが付くため、
  // img.photo:not(.card-img-top) で実サムネイル枠だけを対象にする。
  function findMaterialThumbnailFrame(scope) {
    if (!scope) return null;
    return scope.querySelector('img.photo:not(.card-img-top)');
  }

  function getMaterialTitleInfo(scope, viewMode) {
    if (!scope) return { available: false, value: '' };

    if (viewMode !== 'list') {
      var title = scope.querySelector('p.m-0');
      if (!title) return { available: false, value: '' };
      return { available: true, value: (title.textContent || '').trim() };
    }

    var table = scope.closest && scope.closest('table.search-list');
    if (!table) return { available: false, value: '' };
    var headers = Array.from(table.querySelectorAll('thead th, thead td')).filter(function (cell) {
      return (cell.innerText || cell.textContent || '').trim() === '素材タイトル';
    });
    if (headers.length !== 1) return { available: false, value: '' };

    var index = headers[0].cellIndex;
    var cell = scope.cells && scope.cells[index];
    if (!cell) return { available: false, value: '' };
    return { available: true, value: (cell.textContent || '').trim() };
  }

  // リスト表示の日付は、画面種別ごとの内部DOM(class等)に依存せず、
  // ヘッダ名から列位置を特定して同一行のセル文字列を取得する。
  // 「削除日」「預入日」列は任意扱いとし、列が無い場合もツール実行は妨げない。
  function getListColumnText(scope, label) {
    if (!scope || !scope.closest) return { available: false, value: '' };
    var table = scope.closest('table.search-list');
    if (!table) return { available: false, value: '' };
    var headers = Array.from(table.querySelectorAll('thead th, thead td')).filter(function (cell) {
      return (cell.innerText || cell.textContent || '').trim() === label;
    });
    if (headers.length !== 1) return { available: false, value: '' };

    var index = headers[0].cellIndex;
    var cell = scope.cells && scope.cells[index];
    if (!cell) return { available: false, value: '' };
    return { available: true, value: String(cell.textContent || '').trim() };
  }

  function normalizeListDateDisplay(raw) {
    var text = String(raw == null ? '' : raw).trim();
    if (!text || text === '-' || text === '—') return '';
    var m = text.match(/^(\d{4})[\/-](\d{1,2})[\/-](\d{1,2})$/);
    if (!m) return text;
    return m[1] + '/' + String(Number(m[2])).padStart(2, '0') + '/' +
      String(Number(m[3])).padStart(2, '0');
  }

  function getListDateInfo(scope, viewMode, label) {
    if (viewMode !== 'list') return { available: false, value: '' };
    var info = getListColumnText(scope, label);
    return {
      available: !!info.available,
      value: info.available ? normalizeListDateDisplay(info.value) : ''
    };
  }

  function hasBlankThumbnailFrame(scope) {
    var thumbnail = findMaterialThumbnailFrame(scope);
    if (!thumbnail) return false;

    // getAttribute('src') は、属性なしなら null、src="" なら空文字を返す。
    // どちらも「白サムネイル」として扱う。img.src はURLへ解決されるため使わない。
    var src = thumbnail.getAttribute('src');
    return src == null || String(src).trim() === '';
  }

  function getUniqueMaterialTitleColumnIndex(table) {
    if (!table) return -1;
    var headers = Array.from(table.querySelectorAll('thead th, thead td')).filter(function (cell) {
      return (cell.innerText || cell.textContent || '').trim() === '素材タイトル';
    });
    return headers.length === 1 ? headers[0].cellIndex : -1;
  }

  function makeUnknownFingerprint(scope, order) {
    var text = String((scope && (scope.innerText || scope.textContent)) || '')
      .replace(/\s+/g, ' ').trim().slice(0, 240);
    var hash = 2166136261;
    for (var i = 0; i < text.length; i++) {
      hash ^= text.charCodeAt(i);
      hash = Math.imul(hash, 16777619);
    }
    return 'unknown:' + order + ':' + (hash >>> 0).toString(16);
  }

  function textContainsMaterialKey(text, key) {
    if (!text || !key) return false;
    var tokens = String(text).toUpperCase().match(/[A-Z0-9]+(?:-[A-Z0-9]+)*/g) || [];
    return tokens.some(function (token) {
      var normalized = normalizeMaterialNo(token);
      return !!normalized && normalized.key === key;
    });
  }

  function addLocalDays(baseDate, days) {
    var d = new Date(baseDate.getFullYear(), baseDate.getMonth(), baseDate.getDate());
    d.setDate(d.getDate() + days);
    return d;
  }

  function isoLocal(d) {
    return d.getFullYear() + '-' +
      String(d.getMonth() + 1).padStart(2, '0') + '-' +
      String(d.getDate()).padStart(2, '0');
  }

  function displayIso(iso) {
    return iso ? iso.replace(/-/g, '/') : '-';
  }

  function fatalError(message) {
    var e = new Error(message);
    e.__cvFatal = true;
    return e;
  }

  // ===== Worker タイマー =====================================================
  function ensureTimer() {
    if (sleep) return;
    try {
      var blob = new Blob(['onmessage=e=>{setTimeout(()=>postMessage(e.data.id),e.data.ms)}']);
      var objectUrl = URL.createObjectURL(blob);
      worker = new Worker(objectUrl);
      URL.revokeObjectURL(objectUrl);
      var cbs = new Map();
      var seq = 0;
      worker.onmessage = function (e) {
        var cb = cbs.get(e.data);
        cbs.delete(e.data);
        if (cb) cb();
      };
      sleep = function (ms) {
        return new Promise(function (resolve) {
          var id = ++seq;
          cbs.set(id, resolve);
          worker.postMessage({ id: id, ms: ms });
        });
      };
    } catch (e) {
      // Worker が使えない環境では通常の setTimeout にフォールバックする。
      sleep = function (ms) {
        return new Promise(function (resolve) { setTimeout(resolve, ms); });
      };
    }
  }

  function finishTimer() {
    if (worker) {
      worker.terminate();
      worker = null;
    }
    sleep = null;
  }

  async function waitFor(fn, timeoutMs, desc) {
    ensureTimer();
    var t0 = Date.now();
    while (Date.now() - t0 < timeoutMs) {
      var v = null;
      try {
        v = fn();
      } catch (e) {
        // 明示的な致命エラーのみ即時伝播し、Blazor再描画中の一時例外は従来通り無視する。
        if (e && e.__cvFatal) throw e;
      }
      if (v) return v;
      await sleep(POLL_MS);
    }
    throw new Error('タイムアウト: ' + desc);
  }

  // ===== 画面判定・素材収集 ==================================================
  function getScreenInfo() {
    var twoPane =
      (visible(document.querySelector('#MaterialListPart')) &&
       visible(document.querySelector('#materialListPart'))) ||
      /^\/material\/search\/container\//i.test(location.pathname) ||
      /^\/material\/container\/search\//i.test(location.pathname);

    if (twoPane) {
      return { ok: false, message: '2画面モードを解除してから実行してください' };
    }

    var screen =
      location.pathname.startsWith('/material/search') ? 'search' :
      location.pathname.startsWith('/material/container') ? 'container' : null;

    if (!screen) {
      return {
        ok: false,
        message: '素材をホイミする場合は\nwebCVの素材検索画面またはコンテナ画面で\n実行してください。'
      };
    }

    var groupSel = Array.from(document.querySelectorAll('select')).find(function (s) {
      return /bg-menu-user-group/.test(String(s.className)) && s.getBoundingClientRect().width > 0;
    });
    var groupName = groupSel && groupSel.selectedOptions[0]
      ? groupSel.selectedOptions[0].text.trim() : null;

    if (groupName !== 'CV収録送出') {
      return {
        ok: false,
        message: 'CV収録送出グループを選択してください' +
          (groupName ? '\n(現在の選択: ' + groupName + ')' : '\n(グループ選択を確認できませんでした)')
      };
    }

    return {
      ok: true,
      screen: screen,
      screenDesc: screen === 'search' ? '素材検索画面' : 'コンテナ画面',
      groupName: groupName
    };
  }

  function getVisibleMaterialRoot(screen) {
    var selector = screen === 'container' ? '#materialListPart' : null;
    if (!selector) return null;
    return Array.from(document.querySelectorAll(selector)).find(function (el) {
      return visible(el);
    }) || null;
  }

  function getSearchSectionRoots() {
    var defs = [
      { selector: '#MaterialListPart', materialType: 'original', materialTypeLabel: '元素材' },
      { selector: '#OAListPart', materialType: 'oa', materialTypeLabel: 'OA素材' }
    ];
    var sections = [];
    var collapsed = [];

    defs.forEach(function (def) {
      var nodes = Array.from(document.querySelectorAll(def.selector));
      var root = nodes.find(function (el) { return visible(el); }) || null;
      if (root) {
        sections.push({
          root: root,
          materialType: def.materialType,
          materialTypeLabel: def.materialTypeLabel
        });
      } else if (nodes.some(function (el) { return /(^|\s)d-none(\s|$)/.test(String(el.className || '')); })) {
        // 実機では検索条件OFFならDOM自体が消え、折りたたみ時はroot自身にd-noneが付く。
        // SPA遷移で残った不可視DOMを折りたたみと誤認しないため、d-noneを明示確認する。
        collapsed.push(def.materialTypeLabel);
      }
    });

    return { sections: sections, collapsed: collapsed };
  }

  function collectTiles(screen) {
    if (screen === 'search') {
      var searchRoots = getSearchSectionRoots();

      if (searchRoots.collapsed.length > 0) {
        return {
          ok: false,
          message: searchRoots.collapsed.join('・') +
            'セクションが折りたたまれています。対象セクションを展開してから再実行してください。'
        };
      }

      if (searchRoots.sections.length === 0) {
        return {
          ok: true,
          viewMode: 'unknown',
          viewDesc: '表示モード不明',
          entries: []
        };
      }

      // 元素材/OA素材の表示モードは同時に切り替わる。
      // いずれかのセクションに可視search-listがあればリスト表示として収集する。
      var listMode = searchRoots.sections.some(function (section) {
        return Array.from(section.root.querySelectorAll('table.search-list')).some(function (table) {
          return visible(table);
        });
      });

      var searchEntries = [];

      if (listMode) {
        for (var si = 0; si < searchRoots.sections.length; si++) {
          var section = searchRoots.sections[si];
          var tables = Array.from(section.root.querySelectorAll('table.search-list')).filter(function (table) {
            return visible(table);
          });

          if (tables.length > 1) {
            return {
              ok: false,
              message: section.materialTypeLabel +
                'のリスト表示テーブルを複数検出しました。画面を再読み込みしてから再実行してください。'
            };
          }

          if (tables.length === 0) {
            // 0件セクションは可視テーブル自体が無い場合があるため、素材らしい可視要素が無ければ許容する。
            var hasVisibleMaterial = Array.from(section.root.querySelectorAll('img.photo, span.h6')).some(function (el) {
              return visible(el);
            });
            if (hasVisibleMaterial) {
              return {
                ok: false,
                message: section.materialTypeLabel +
                  'の表示モードを正しく判定できません。検索結果を再表示してから再実行してください。'
              };
            }
            continue;
          }

          var listTable = tables[0];
          var rows = Array.from(listTable.tBodies || []).reduce(function (all, tbody) {
            return all.concat(Array.from(tbody.rows || []));
          }, []).filter(function (row) {
            return visible(row);
          });

          // 0件セクションには判定対象素材が無いため列要件を課さない。
          if (rows.length > 0 && getUniqueMaterialTitleColumnIndex(listTable) < 0) {
            return {
              ok: false,
              message: section.materialTypeLabel +
                'のリスト表示で「素材タイトル」列を確認できません。\n' +
                '表示項目設定で「素材タイトル」を表示してから再実行してください。'
            };
          }

          rows.forEach(function (row) {
            searchEntries.push({
              element: row,
              materialType: section.materialType,
              materialTypeLabel: section.materialTypeLabel
            });
          });
        }

        return {
          ok: true,
          viewMode: 'list',
          viewDesc: 'リスト表示',
          entries: searchEntries
        };
      }

      searchRoots.sections.forEach(function (section) {
        var cards = [];
        if (section.materialType === 'original') {
          cards = Array.from(section.root.querySelectorAll('.draggable-tag'))
            .filter(function (el) { return visible(el); });
        } else {
          // OA素材は .draggable-tag を持たないため、実測DOM構造でタイルを特定する。
          cards = Array.from(section.root.querySelectorAll('div.d-block.position-relative')).filter(function (el) {
            var hasStructure = !!el.querySelector('img.photo') &&
              !!el.querySelector('span.h6') && !!el.querySelector('p.m-0');
            return visible(el) && hasStructure &&
              !(el.parentElement && el.parentElement.closest('div.d-block.position-relative'));
          });
        }

        cards.forEach(function (card) {
          searchEntries.push({
            element: card,
            materialType: section.materialType,
            materialTypeLabel: section.materialTypeLabel
          });
        });
      });

      return {
        ok: true,
        viewMode: 'thumbnail',
        viewDesc: 'サムネイル表示',
        entries: searchEntries
      };
    }

    var root = getVisibleMaterialRoot(screen);
    if (!root) {
      return {
        ok: true,
        viewMode: 'unknown',
        viewDesc: '表示モード不明',
        entries: []
      };
    }

    // webCVはサムネイル/リスト両方のDOMを常時保持し、.d-none等で切り替える。
    var listTable = Array.from(root.querySelectorAll('table.search-list')).find(function (table) {
      return visible(table);
    }) || null;

    if (listTable) {
      if (getUniqueMaterialTitleColumnIndex(listTable) < 0) {
        return {
          ok: false,
          message: 'コンテナのリスト表示で「素材タイトル」列を確認できません。\n' +
            '表示項目設定で「素材タイトル」を表示してから再実行してください。'
        };
      }

      var rows = Array.from(listTable.tBodies || []).reduce(function (all, tbody) {
        return all.concat(Array.from(tbody.rows || []));
      }, []).filter(function (row) {
        return visible(row);
      });

      return {
        ok: true,
        viewMode: 'list',
        viewDesc: 'リスト表示',
        entries: rows.map(function (row) {
          return { element: row, materialType: 'container', materialTypeLabel: 'コンテナ' };
        })
      };
    }

    // コンテナ・サムネイルでは素材番号の書式を素材収集条件にしない。
    var cards = Array.from(root.querySelectorAll('div.nonSelect.d-block')).filter(function (el) {
      var hasCardStructure = el.matches('.tableBorderBlack') || !!el.querySelector('.tableBorderBlack') ||
        !!el.querySelector('span.h6') || !!el.querySelector('img.photo');
      return visible(el) && hasCardStructure &&
        !(el.parentElement && el.parentElement.closest('div.nonSelect.d-block'));
    });

    if (cards.length === 0) {
      cards = Array.from(root.querySelectorAll('.tableBorderBlack')).filter(function (t) {
        return visible(t) &&
          !(t.parentElement && t.parentElement.closest('.tableBorderBlack')) &&
          (!!t.querySelector('span.h6') || !!t.querySelector('img.photo'));
      });
    }

    return {
      ok: true,
      viewMode: 'thumbnail',
      viewDesc: 'サムネイル表示',
      entries: cards.map(function (card) {
        return { element: card, materialType: 'container', materialTypeLabel: 'コンテナ' };
      })
    };
  }

  function buildMaterialState(screen) {
    var collected = collectTiles(screen);
    if (!collected.ok) return collected;

    var entries = collected.entries || [];
    if (entries.length === 0) {
      return {
        ok: false,
        message: screen === 'search'
          ? '検索結果の素材が表示されていません。元素材またはOA素材を検索してから実行してください。'
          : 'コンテナが選択されていないか、素材がありません。\n特定のコンテナを開いて素材を表示してから実行してください。'
      };
    }

    var items = entries.map(function (entry, order) {
      var tile = entry.element;
      var noInfo = getMaterialNo(tile, collected.viewMode);
      var noValue = noInfo.value;
      var isError = Array.from(tile.querySelectorAll('.badge')).some(function (b) {
        return /badgeOrange/.test(b.className) || /\bError\b/.test(b.innerText);
      });
      var previewTrigger = findPreviewTrigger(tile, collected.viewMode);
      var titleInfo = getMaterialTitleInfo(tile, collected.viewMode);
      var deleteDateInfo = getListDateInfo(tile, collected.viewMode, '削除日');
      var depositDateInfo = getListDateInfo(tile, collected.viewMode, '預入日');
      var blankThumbnail = titleInfo.available && titleInfo.value === '' && hasBlankThumbnailFrame(tile);

      var unknownReason = '';
      if (!titleInfo.available) {
        unknownReason = '素材タイトルを取得できない';
      } else if (!noValue) {
        unknownReason = noInfo.reason || '素材番号を取得できない';
      } else if (collected.viewMode === 'list' && !previewTrigger) {
        unknownReason = 'プレビュー起動要素(サムネイル画像)を取得できない';
      }

      var fallbackText = String(tile.innerText || tile.textContent || '')
        .split(/\r?\n/).map(function (v) { return v.trim(); }).filter(Boolean).slice(0, 2).join(' / ');

      return {
        order: order,
        tile: tile,
        previewTrigger: previewTrigger,
        no: noValue ? noValue.display : null,
        noKey: noValue ? noValue.key : null,
        noSource: noInfo.source || null,
        materialType: entry.materialType || (screen === 'search' ? 'original' : 'container'),
        materialTypeLabel: entry.materialTypeLabel || (screen === 'search' ? '元素材' : 'コンテナ'),
        titleAvailable: !!titleInfo.available,
        title: titleInfo.available ? titleInfo.value : null,
        listDeleteDateAvailable: !!deleteDateInfo.available,
        listDeleteDate: deleteDateInfo.available ? deleteDateInfo.value : '',
        listDepositDateAvailable: !!depositDateInfo.available,
        listDepositDate: depositDateInfo.available ? depositDateInfo.value : '',
        blankThumbnail: !!blankThumbnail,
        fallbackLabel: fallbackText ? fallbackText.slice(0, 90) : '(番号不明 #' + (order + 1) + ')',
        fingerprint: noValue ? 'material:' + noValue.key : makeUnknownFingerprint(tile, order),
        isError: isError,
        unknownReason: unknownReason,
        kind: null
      };
    });

    var seenNo = new Set();
    var targets = [];
    var duplicates = [];
    var excluded = [];
    var blankThumbnails = [];
    var emptyTitles = [];
    var unknown = [];

    items.forEach(function (item) {
      // 優先順: Error → 白サムネ+タイトル空 → タイトル空 → unknown → 重複 → target
      if (item.isError) {
        item.kind = 'excluded';
        excluded.push(item);
        return;
      }
      if (item.titleAvailable && item.title === '' && item.blankThumbnail) {
        item.kind = 'blankThumbnail';
        blankThumbnails.push(item);
        return;
      }
      if (item.titleAvailable && item.title === '') {
        item.kind = 'emptyTitle';
        emptyTitles.push(item);
        return;
      }
      if (!item.titleAvailable || !item.noKey ||
          (collected.viewMode === 'list' && !item.previewTrigger)) {
        item.kind = 'unknown';
        unknown.push(item);
        return;
      }
      if (seenNo.has(item.noKey)) {
        item.kind = 'duplicate';
        duplicates.push(item);
        return;
      }
      seenNo.add(item.noKey);
      item.kind = 'target';
      targets.push(item);
    });

    var originalCount = items.filter(function (item) { return item.materialType === 'original'; }).length;
    var oaCount = items.filter(function (item) { return item.materialType === 'oa'; }).length;

    return {
      ok: true,
      viewMode: collected.viewMode,
      viewDesc: collected.viewDesc,
      items: items,
      targets: targets,
      duplicates: duplicates,
      excluded: excluded,
      blankThumbnails: blankThumbnails,
      emptyTitles: emptyTitles,
      unknown: unknown,
      originalCount: originalCount,
      oaCount: oaCount
    };
  }

  function captureContext() {
    var screenInfo = getScreenInfo();
    if (!screenInfo.ok) return screenInfo;
    var materialState = buildMaterialState(screenInfo.screen);
    if (!materialState.ok) return materialState;
    return Object.assign({}, screenInfo, materialState);
  }

  function makeSnapshot(ctx) {
    return {
      screen: ctx.screen,
      viewMode: ctx.viewMode,
      groupName: ctx.groupName,
      items: ctx.items.map(function (i) {
        return {
          order: i.order,
          no: i.no || null,
          noKey: i.noKey || null,
          materialType: i.materialType || null,
          fingerprint: i.fingerprint,
          listDeleteDate: ctx.viewMode === 'list' ? (i.listDeleteDate || '') : null,
          listDepositDate: ctx.viewMode === 'list' ? (i.listDepositDate || '') : null,
          isError: !!i.isError,
          kind: i.kind,
          hasPreviewTrigger: !!i.previewTrigger
        };
      })
    };
  }

  function snapshotsEqual(a, b) {
    return JSON.stringify(a) === JSON.stringify(b);
  }

  // ===== UI ==================================================================
  function createUi() {
    // Blazor enhanced navigation では、document/window を維持したまま body のDOMが
    // 差し替えられ、ブックマークレットが追加したhostだけが除去されることがある。
    // host参照が残っていてもDOM未接続ならstale状態なので、UIを完全に作り直す。
    if (host && host.isConnected) return;
    if (host) {
      console.warn('[CV日付一括設定] UIホストがDOMから切り離されているため再構築します。');
      try { host.remove(); } catch (e) { /* 既に切り離し済みなら無視 */ }
      host = null;
      shadow = null;
      rowEls.clear();
    }

    host = document.createElement('div');
    host.id = 'cv-date-batch-tool-host';
    host.style.cssText = 'all:initial;position:fixed;z-index:2147483647;';
    shadow = host.attachShadow({ mode: 'open' });

    shadow.innerHTML = [
      '<style>',
      ':host{all:initial}',
      '*{box-sizing:border-box}',
      '.overlay{position:fixed;top:0;left:0;right:0;bottom:0;z-index:2147483647;background:rgba(15,23,42,.52);display:flex;align-items:center;justify-content:center;padding:18px;font-family:"Hiragino Sans","Yu Gothic UI","Meiryo",sans-serif;color:#1e293b;font-size:14px}',
      '.panel{width:1196px;max-width:96vw;height:88vh;max-height:900px;min-height:560px;background:#fff;border-radius:12px;box-shadow:0 24px 80px rgba(0,0,0,.42);display:flex;flex-direction:column;overflow:hidden}',
      '.titlebar{flex:0 0 auto;background:#0f766e;color:#fff;padding:13px 17px;display:flex;align-items:center;gap:12px}',
      '.titlebar h1{font-size:16px;font-weight:700;margin:0;flex:1}',
      '.version{font-size:11px;opacity:.82}',
      '.xbtn{border:0;background:transparent;color:#fff;font-size:21px;line-height:1;padding:2px 6px;border-radius:4px;cursor:pointer}',
      '.xbtn:hover{background:rgba(255,255,255,.18)}',
      '.xbtn:disabled{opacity:.35;cursor:not-allowed}',
      '.top{flex:0 0 auto;padding:14px 16px 12px;border-bottom:1px solid #e2e8f0;background:#fff}',
      '.context{display:flex;gap:14px;flex-wrap:wrap;color:#475569;font-size:12px;margin-bottom:10px}',
      '.config{display:grid;grid-template-columns:minmax(250px,1.35fr) minmax(180px,.8fr) minmax(180px,.8fr);gap:12px;align-items:end}',
      '.field-label{display:block;font-size:12px;font-weight:700;color:#475569;margin-bottom:5px}',
      '.radios{display:flex;gap:14px;min-height:36px;align-items:center;flex-wrap:wrap}',
      '.radio{display:inline-flex;align-items:center;gap:6px;cursor:pointer;white-space:nowrap}',
      '.radio input{accent-color:#0f766e}',
      'input[type=date]{width:100%;height:36px;border:1px solid #cbd5e1;border-radius:7px;padding:5px 9px;font:inherit;background:#fff;color:#1e293b;cursor:pointer}',
      'input[type=date]:focus{outline:2px solid #0f766e;outline-offset:-1px}',
      'input[type=date]:disabled{background:#f1f5f9;color:#94a3b8}',
      'input[type=date].required-empty{border-color:#dc2626;background:#fff7f7;box-shadow:0 0 0 1px #dc2626 inset}',
      'input[type=date].required-empty:focus{outline:2px solid #dc2626;outline-offset:-1px}',
      '.rule{margin-top:8px;font-size:12px;color:#64748b}',
      '.validation{min-height:18px;margin-top:4px;font-size:12px;color:#b91c1c;font-weight:600}',
      '.summary{flex:0 0 auto;padding:12px 16px;border-bottom:1px solid #e2e8f0;background:#f8fafc}',
      '.summary-head{display:flex;align-items:center;gap:10px;margin-bottom:8px}',
      '.state-title{font-size:14px;font-weight:700;flex:1}',
      '.current{font-size:12px;color:#475569;max-width:46%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}',
      '.progress-line{display:flex;align-items:center;gap:10px}',
      '.progress-track{height:10px;background:#e2e8f0;border-radius:999px;overflow:hidden;flex:1}',
      '.progress-bar{height:100%;width:0;background:#0f766e;transition:width .15s ease}',
      '.progress-text{font-size:12px;font-weight:700;min-width:90px;text-align:right}',
      '.counts{display:flex;gap:10px;flex-wrap:wrap;margin-top:9px;font-size:12px}',
      '.pill{border-radius:999px;padding:4px 9px;background:#fff;border:1px solid #cbd5e1}',
      '.pill strong{font-size:13px}',
      '.pill.success{border-color:#86efac;color:#166534}',
      '.pill.skip{border-color:#fde68a;color:#92400e}',
      '.pill.fail{border-color:#fecaca;color:#991b1b}',
      '.pill.exclude{border-color:#cbd5e1;color:#475569}',
      '.message{display:none;margin-top:9px;border-radius:7px;padding:8px 10px;font-size:12px}',
      '.message.show{display:block}',
      '.message.error{background:#fef2f2;border:1px solid #fecaca;color:#991b1b}',
      '.message.info{background:#eff6ff;border:1px solid #bfdbfe;color:#1e40af}',
      '.message.warn{background:#fffbeb;border:1px solid #fde68a;color:#92400e;font-weight:600}',
      '.list-wrap{flex:1 1 auto;min-height:0;display:flex;flex-direction:column;background:#fff;overflow-x:auto;overflow-y:hidden}',
      '.list-head,.result-row{display:grid;grid-template-columns:36px 120px 400px 140px 80px 100px 320px;align-items:center}',
      '.list-head{flex:0 0 auto;min-width:1196px;background:#f1f5f9;border-bottom:1px solid #cbd5e1;font-size:11px;font-weight:700;color:#475569}',
      '.list-head>div{padding:8px 10px;border-right:1px solid #e2e8f0}',
      '.sortable-col{display:flex;align-items:center;gap:6px;cursor:pointer;user-select:none;outline:none}',
      '.sortable-col:hover{background:#e2e8f0;color:#334155}',
      '.sortable-col:focus-visible{box-shadow:inset 0 0 0 2px #0f766e}',
      '.sortable-col.active{background:#ccfbf1;color:#0f766e}',
      '.sortable-col.sort-disabled{cursor:not-allowed;opacity:.55}',
      '.sortable-col.sort-disabled:hover{background:inherit;color:inherit}',
      '.sort-indicator{margin-left:auto;min-width:12px;text-align:center;font-size:10px;color:#94a3b8}',
      '.sortable-col.active .sort-indicator{color:#0f766e}',
      '.list-scroll{flex:1 1 auto;min-height:0;min-width:1196px;overflow-y:auto;overscroll-behavior:contain}',
      '.result-row{min-height:42px;border-bottom:1px solid #eef2f7;font-size:12px}',
      '.result-row>div{padding:8px 10px;min-width:0;overflow-wrap:anywhere}',
      '.select-col{display:flex;align-items:center;justify-content:center;padding:0!important;min-width:0}',
      '.select-col input{width:16px;height:16px;margin:0;accent-color:#0f766e;cursor:pointer}',
      '.select-col input:disabled{cursor:not-allowed;opacity:.45}',
      '.select-all-cell{cursor:pointer}',
      '.result-row.processing{background:#ecfeff}',
      '.result-row.success{background:#f0fdf4}',
      '.result-row.fail{background:#fef2f2}',
      '.result-row.skip{background:#fffbeb}',
      '.result-row.excluded{background:#f8fafc;color:#64748b}',
      '.material{font-family:"MS Gothic","Consolas",monospace;font-weight:700;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
      '.material-title{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
      '.status,.del,.dep{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
      '.status-badge{display:inline-flex;align-items:center;gap:5px;font-weight:700}',
      '.muted{color:#94a3b8}',
      '.footer{flex:0 0 auto;border-top:1px solid #e2e8f0;padding:10px 16px;background:#fff;display:flex;align-items:center;gap:8px}',
      '.footer-note{font-size:11px;color:#64748b;flex:1}',
      '.btn{border:1px solid #cbd5e1;background:#fff;color:#1e293b;border-radius:7px;padding:8px 15px;font:inherit;font-size:13px;cursor:pointer}',
      '.btn:hover{background:#f1f5f9}',
      '.btn-primary{background:#0f766e;color:#fff;border-color:#0f766e;font-weight:700}',
      '.btn-primary:hover{background:#0d5f59}',
      '.btn:disabled{opacity:.45;cursor:not-allowed}',
      '.btn:disabled:hover{background:inherit}',
      '@media(max-width:760px){.panel{height:94vh;max-width:98vw}.config{grid-template-columns:1fr 1fr}.mode-field{grid-column:1/-1}.list-head,.result-row{grid-template-columns:36px 120px 360px 130px 80px 100px 280px}.list-head,.list-scroll{min-width:1106px}}',
      '</style>',
      '<div class="overlay">',
      '  <div class="panel" role="dialog" aria-modal="true" aria-label="素材をホイミする">',
      '    <div class="titlebar">',
      '      <h1>素材をホイミする</h1>',
      '      <span class="version">Ver. ' + TOOL_VERSION + '</span>',
      '      <button class="xbtn" id="btn-x" aria-label="閉じる" title="閉じる">×</button>',
      '    </div>',
      '    <div class="top">',
      '      <div class="context"><span id="screen-info"></span><span>グループ: CV収録送出</span><span id="detected-info"></span></div>',
      '      <div class="config" id="config-area">',
      '        <div class="mode-field"><span class="field-label">処理モード</span><div class="radios"><label class="radio"><input type="radio" name="mode" value="2" checked> 削除日＋預入日を更新</label><label class="radio"><input type="radio" name="mode" value="1"> 削除日のみ更新</label></div></div>',
      '        <label><span class="field-label">削除日</span><input type="date" id="delete-date" required aria-required="true"></label>',
      '        <label><span class="field-label">預入日</span><input type="date" id="deposit-date"></label>',
      '      </div>',
      '      <div class="rule"><strong>削除日は入力必須</strong>です。「削除日＋預入日を更新」では<strong>預入日も入力必須</strong>です。日付ルール: 削除日・預入日はツール実行日以降、かつ 削除日 &gt; 預入日。</div>',
      '      <div class="validation" id="validation"></div>',
      '    </div>',
      '    <div class="summary">',
      '      <div class="summary-head"><div class="state-title" id="state-title">実行内容を確認してください</div><div class="current" id="current"></div></div>',
      '      <div class="progress-line"><div class="progress-track"><div class="progress-bar" id="progress-bar"></div></div><div class="progress-text" id="progress-text">0 / 0件</div></div>',
      '      <div class="counts"><span class="pill success">成功 <strong id="count-success">0</strong></span><span class="pill skip">スキップ <strong id="count-skip">0</strong></span><span class="pill fail">失敗 <strong id="count-fail">0</strong></span><span class="pill exclude">除外 <strong id="count-exclude">0</strong></span></div>',
      '      <div class="message" id="message"></div>',
      '    </div>',
      '    <div class="list-wrap">',
      '      <div class="list-head"><div class="select-col select-all-cell" id="select-all-cell" title="処理対象を全選択 / 全解除"><input type="checkbox" id="select-all" aria-label="処理対象を全選択または全解除"></div><div class="sortable-col" data-sort-key="no" role="button" tabindex="0" aria-sort="none"><span>素材番号</span><span class="sort-indicator" aria-hidden="true">↕</span></div><div class="sortable-col" data-sort-key="title" role="button" tabindex="0" aria-sort="none"><span>素材タイトル</span><span class="sort-indicator" aria-hidden="true">↕</span></div><div class="sortable-col" data-sort-key="status" role="button" tabindex="0" aria-sort="none"><span>結果 / 状態</span><span class="sort-indicator" aria-hidden="true">↕</span></div><div class="sortable-col" data-sort-key="delNote" role="button" tabindex="0" aria-sort="none"><span>削除日</span><span class="sort-indicator" aria-hidden="true">↕</span></div><div class="sortable-col" data-sort-key="depNote" role="button" tabindex="0" aria-sort="none"><span>預入日</span><span class="sort-indicator" aria-hidden="true">↕</span></div><div class="sortable-col" data-sort-key="reason" role="button" tabindex="0" aria-sort="none"><span>詳細</span><span class="sort-indicator" aria-hidden="true">↕</span></div></div>',
      '      <div class="list-scroll" id="list-scroll"></div>',
      '    </div>',
      '    <div class="footer">',
      '      <div class="footer-note" id="footer-note">実行中はこのタブを閉じたり、webCVを操作しないでください。</div>',
      '      <button class="btn" id="btn-close">閉じる</button>',
      '      <button class="btn btn-primary" id="btn-run">ホイミ</button>',
      '    </div>',
      '  </div>',
      '</div>'
    ].join('');

    document.body.appendChild(host);

    $('btn-x').addEventListener('click', closeTool);
    $('btn-close').addEventListener('click', closeTool);
    $('btn-run').addEventListener('click', startRun);
    $('delete-date').addEventListener('input', function () {
      autoFillDepositDateIfNeeded();
      validateConfig();
    });
    $('delete-date').addEventListener('change', function () {
      autoFillDepositDateIfNeeded();
      validateConfig();
    });
    $('deposit-date').addEventListener('input', validateConfig);
    $('deposit-date').addEventListener('change', validateConfig);
    $('delete-date').addEventListener('click', function () { openNativeDatePicker($('delete-date')); });
    $('deposit-date').addEventListener('click', function () { openNativeDatePicker($('deposit-date')); });
    $('select-all').addEventListener('change', function () { toggleAllTargetSelection($('select-all').checked); });
    $('select-all-cell').addEventListener('click', function (e) {
      if (running || $('select-all').disabled || e.target === $('select-all')) return;
      $('select-all').click();
    });
    Array.from(shadow.querySelectorAll('.sortable-col')).forEach(function (el) {
      el.addEventListener('click', function () { cycleSort(el.dataset.sortKey); });
      el.addEventListener('keydown', function (e) {
        if (e.key !== 'Enter' && e.key !== ' ') return;
        e.preventDefault();
        cycleSort(el.dataset.sortKey);
      });
    });
    Array.from(shadow.querySelectorAll('input[name="mode"]')).forEach(function (el) {
      el.addEventListener('change', function () {
        $('deposit-date').disabled = getMode() !== '2';
        autoFillDepositDateIfNeeded();
        validateConfig();
      });
    });

    shadow.addEventListener('keydown', function (e) {
      if (e.key === 'Escape' && !running) closeTool();
    });
  }

  function $(id) {
    return shadow.getElementById(id);
  }

  function getMode() {
    var checked = shadow.querySelector('input[name="mode"]:checked');
    return checked ? checked.value : '2';
  }

  // モード2で預入日が未入力の場合のみ、削除日の前日を補完する。
  // ユーザーが入力済みの預入日は自動変更せず、前日が実行日より前になる場合も補完しない。
  function autoFillDepositDateIfNeeded() {
    if (!shadow || getMode() !== '2') return false;

    var deleteInput = $('delete-date');
    var depositInput = $('deposit-date');
    if (!deleteInput || !depositInput || !deleteInput.value || depositInput.value) return false;

    var parts = deleteInput.value.split('-').map(Number);
    if (parts.length !== 3 || !parts[0] || !parts[1] || !parts[2]) return false;

    var deleteDate = new Date(parts[0], parts[1] - 1, parts[2]);
    var previousIso = isoLocal(addLocalDays(deleteDate, -1));
    if (executionDateIso && previousIso < executionDateIso) return false;

    depositInput.value = previousIso;
    return true;
  }

  function openNativeDatePicker(input) {
    if (!input || input.disabled) return;
    if (typeof input.showPicker === 'function') {
      try {
        input.showPicker();
        return;
      } catch (e) {}
    }
    input.focus();
  }

  function setMessage(text, kind) {
    var el = $('message');
    if (!text) {
      el.textContent = '';
      el.className = 'message';
      return;
    }
    el.textContent = text;
    el.className = 'message show ' + (kind || 'info');
  }

  function updateRequiredDateState(mode, del, dep) {
    var deleteInput = $('delete-date');
    var depositInput = $('deposit-date');
    var depositRequired = mode === '2';

    deleteInput.required = true;
    deleteInput.setAttribute('aria-required', 'true');
    deleteInput.classList.toggle('required-empty', !del);
    deleteInput.setAttribute('aria-invalid', !del ? 'true' : 'false');

    depositInput.required = depositRequired;
    depositInput.setAttribute('aria-required', depositRequired ? 'true' : 'false');
    depositInput.classList.toggle('required-empty', depositRequired && !dep);
    depositInput.setAttribute('aria-invalid', depositRequired && !dep ? 'true' : 'false');
  }

  function getTargetModels() {
    return rowModels.filter(function (r) { return r.kind === 'target'; });
  }

  function getSelectedTargetModels() {
    return getTargetModels().filter(function (r) { return !!r.selected; });
  }

  function getSelectedTargetCount() {
    return getSelectedTargetModels().length;
  }

  function updateDetectedInfo() {
    if (!currentContext || !shadow) return;
    var typeBreakdown = currentContext.screen === 'search'
      ? '（元素材: ' + currentContext.originalCount + ' / OA素材: ' + currentContext.oaCount + '）'
      : '';
    $('detected-info').textContent =
      '認識: ' + currentContext.items.length + '件' + typeBreakdown + ' / 処理対象: ' + currentContext.targets.length +
      '件 / 選択: ' + getSelectedTargetCount() + '件 / 削除済(白サムネ): ' + currentContext.blankThumbnails.length +
      '件 / タイトル未設定: ' + currentContext.emptyTitles.length +
      '件 / Error除外: ' + currentContext.excluded.length +
      '件 / 重複: ' + currentContext.duplicates.length + '件 / 判定不能: ' + currentContext.unknown.length + '件';
  }

  function updateSelectAllState() {
    if (!shadow) return;
    var checkbox = $('select-all');
    if (!checkbox) return;
    var targets = getTargetModels();
    var selectedCount = targets.filter(function (r) { return !!r.selected; }).length;
    checkbox.checked = targets.length > 0 && selectedCount === targets.length;
    checkbox.indeterminate = selectedCount > 0 && selectedCount < targets.length;
    checkbox.disabled = running || targets.length === 0;
  }

  function refreshPreRunMessage() {
    if (!currentContext || !shadow || running) return;
    var selectedCount = getSelectedTargetCount();
    if (currentContext.targets.length === 0) {
      setMessage(
        '素材は' + currentContext.items.length + '件認識しましたが、処理対象は0件です。削除済・タイトル未設定・判定不能・Error除外などの一覧を確認してください。',
        'warn'
      );
    } else if (selectedCount >= 100) {
      setMessage(
        '選択中の処理対象が' + selectedCount + '件あります。完了まで長時間かかる可能性があります。対象件数を確認してから実行してください。',
        'warn'
      );
    } else {
      setMessage('', 'info');
    }
  }

  function resetTargetModelForSelection(model, selected) {
    model.selected = !!selected;
    if (model.selected) {
      model.final = false;
      model.status = '待機中';
      model.statusClass = '';
      model.delNote = model.initialDelNote;
      model.depNote = model.initialDepNote;
      model.reason = '実行待ち';
    } else {
      model.final = true;
      model.status = 'スキップ(選択解除)';
      model.statusClass = 'skip';
      model.delNote = model.initialDelNote;
      model.depNote = model.initialDepNote;
      model.reason = 'ユーザー操作により処理対象から除外';
    }
  }

  function refreshSelectionUi() {
    updateSelectAllState();
    updateDetectedInfo();
    updateSummary();
    refreshPreRunMessage();
    validateConfig();
  }

  function setTargetSelection(order, selected) {
    if (running) return;
    var model = modelForOrder(order);
    if (!model || model.kind !== 'target') return;
    resetTargetModelForSelection(model, selected);
    paintRow(model);
    refreshSelectionUi();
  }

  function toggleAllTargetSelection(selected) {
    if (running) return;
    getTargetModels().forEach(function (model) {
      resetTargetModelForSelection(model, selected);
      paintRow(model);
    });
    refreshSelectionUi();
  }

  function validateConfig() {
    if (!shadow) return false;
    var mode = getMode();
    var del = $('delete-date').value;
    var dep = $('deposit-date').value;
    var message = '';

    updateRequiredDateState(mode, del, dep);

    if (currentContext && currentContext.targets.length === 0) {
      message = '処理対象の素材がありません。削除済・番号不明・Error除外などの一覧を確認してください。';
    } else if (currentContext && getSelectedTargetCount() === 0) {
      message = 'ホイミ対象の素材を1件以上選択してください。';
    } else if (mode === '2' && !del && !dep) {
      message = '削除日・預入日を選択してください。';
    } else if (!del) {
      message = '削除日を選択してください。';
    } else if (executionDateIso && del < executionDateIso) {
      message = '削除日はツール実行日（' + displayIso(executionDateIso) + '）以降の日付を選択してください。';
    } else if (mode === '2' && !dep) {
      message = '預入日を選択してください。';
    } else if (mode === '2' && executionDateIso && dep < executionDateIso) {
      message = '預入日はツール実行日（' + displayIso(executionDateIso) + '）以降の日付を選択してください。';
    } else if (mode === '2' && del <= dep) {
      message = '削除日は預入日より後の日付にしてください（削除日 > 預入日）。';
    }

    $('validation').textContent = message;
    $('btn-run').disabled = !!message || running;
    return !message;
  }


  // ===== 一覧ソート ==========================================================
  // ソートはツール一覧のDOM表示順だけを変更する。
  // rowModels / currentContext / order は変更せず、実行対象・実処理順・安全照合へ影響させない。
  function isEmptySortValue(value) {
    if (value == null) return true;
    var text = String(value).trim();
    return text === '' || text === '-' || text === '—';
  }

  function getSortValue(model, key) {
    if (!model) return '';
    switch (key) {
      case 'no': return model.no;
      case 'title': return model.title;
      case 'status': return model.status;
      case 'delNote': return model.delNote;
      case 'depNote': return model.depNote;
      case 'reason': return model.reason;
      default: return '';
    }
  }

  function compareSortText(a, b) {
    var aa = String(a);
    var bb = String(b);
    if (sortCollator) return sortCollator.compare(aa, bb);
    return aa.localeCompare(bb);
  }

  function compareModelsForSort(a, b, key, direction) {
    var av = getSortValue(a, key);
    var bv = getSortValue(b, key);
    var aEmpty = isEmptySortValue(av);
    var bEmpty = isEmptySortValue(bv);

    // 値なしは最小値扱い。昇順では先頭、降順では末尾に置く。
    if (aEmpty || bEmpty) {
      if (aEmpty && bEmpty) return a.order - b.order;
      if (direction === 'asc') return aEmpty ? -1 : 1;
      return aEmpty ? 1 : -1;
    }

    var cmp = compareSortText(av, bv);
    if (cmp !== 0) return direction === 'desc' ? -cmp : cmp;

    // 同値は元の画面順(order)で固定し、クリックのたびに順序が揺れないようにする。
    return a.order - b.order;
  }

  function getDisplayModels() {
    var models = rowModels.slice();
    if (!sortState.key || !sortState.direction) {
      return models.sort(function (a, b) { return a.order - b.order; });
    }
    return models.sort(function (a, b) {
      return compareModelsForSort(a, b, sortState.key, sortState.direction);
    });
  }

  function updateSortHeaders() {
    if (!shadow) return;
    Array.from(shadow.querySelectorAll('.sortable-col')).forEach(function (el) {
      var key = el.dataset.sortKey;
      var active = sortState.key === key && !!sortState.direction;
      var indicator = el.querySelector('.sort-indicator');
      el.classList.toggle('active', active);
      el.classList.toggle('sort-disabled', running);
      el.setAttribute('aria-disabled', running ? 'true' : 'false');
      el.setAttribute('aria-sort', active
        ? (sortState.direction === 'asc' ? 'ascending' : 'descending')
        : 'none');
      if (indicator) indicator.textContent = active
        ? (sortState.direction === 'asc' ? '▲' : '▼')
        : '↕';
      el.title = running
        ? '実行中はソートを変更できません'
        : (active
          ? (sortState.direction === 'asc' ? '昇順でソート中。クリックで降順' : '降順でソート中。クリックでソート解除')
          : 'クリックで昇順ソート');
    });
  }

  function applyRowSort() {
    if (!shadow) return;
    var list = $('list-scroll');
    if (!list) return;
    getDisplayModels().forEach(function (model) {
      var row = rowEls.get(model.order);
      if (row) list.appendChild(row);
    });
    updateSortHeaders();
  }

  function cycleSort(key) {
    if (running || !key) return;
    if (sortState.key !== key) {
      sortState = { key: key, direction: 'asc' };
    } else if (sortState.direction === 'asc') {
      sortState = { key: key, direction: 'desc' };
    } else if (sortState.direction === 'desc') {
      sortState = { key: null, direction: null };
    } else {
      sortState = { key: key, direction: 'asc' };
    }
    applyRowSort();
  }

  function rowInitialModel(item) {
    var initialDel = item.listDeleteDate ? item.listDeleteDate : '-';
    var initialDep = item.listDepositDate ? item.listDepositDate : '-';

    if (item.kind === 'blankThumbnail') {
      return {
        order: item.order, no: item.no || item.fallbackLabel || '(番号不明)', kind: item.kind, final: true,
        status: 'スキップ(削除済み)', statusClass: 'skip', delNote: initialDel, depNote: initialDep,
        reason: 'サムネイルが空のため、削除済素材として処理対象外'
      };
    }
    if (item.kind === 'emptyTitle') {
      return {
        order: item.order, no: item.no || item.fallbackLabel || '(番号不明)', kind: item.kind, final: true,
        status: 'スキップ(タイトル未設定)', statusClass: 'skip', delNote: initialDel, depNote: initialDep,
        reason: '素材タイトルが未設定のため処理対象外'
      };
    }
    if (item.kind === 'duplicate') {
      return {
        order: item.order, no: item.no, kind: item.kind, final: true,
        status: 'スキップ(重複)', statusClass: 'skip', delNote: initialDel, depNote: initialDep,
        reason: '同一素材番号のため代表1件のみ処理（更新は全てに反映される）'
      };
    }
    if (item.kind === 'excluded') {
      return {
        order: item.order, no: item.no || item.fallbackLabel || '(番号不明)', kind: item.kind, final: true,
        status: '除外', statusClass: 'excluded', delNote: initialDel, depNote: initialDep,
        reason: 'Error バッジのため対象外'
      };
    }
    if (item.kind === 'unknown') {
      return {
        order: item.order, no: item.no || item.fallbackLabel || '(番号不明)', kind: item.kind, final: true,
        status: 'スキップ', statusClass: 'skip', delNote: initialDel, depNote: initialDep,
        reason: item.unknownReason || '素材番号・素材タイトル・プレビュー起動要素のいずれかを取得できない'
      };
    }
    return {
      order: item.order, no: item.no, kind: item.kind, final: false,
      status: '待機中', statusClass: '', delNote: initialDel, depNote: initialDep, reason: '実行待ち'
    };
  }

  function renderRows(ctx) {
    rowEls.clear();
    rowModels = ctx.items.map(function (item) {
      var model = rowInitialModel(item);
      model.title = item.title == null ? '' : String(item.title);
      model.noKey = item.noKey || null;
      model.initialDelNote = model.delNote;
      model.initialDepNote = model.depNote;
      model.selectable = item.kind === 'target';
      model.selected = model.selectable;
      return model;
    }).sort(function (a, b) { return a.order - b.order; });
    var list = $('list-scroll');
    list.innerHTML = '';

    rowModels.forEach(function (model) {
      var row = document.createElement('div');
      row.className = 'result-row ' + (model.statusClass || '');
      row.dataset.order = String(model.order);
      row.innerHTML =
        '<div class="select-col"><input type="checkbox" class="row-select" aria-label="この素材をホイミ対象にする"></div>' +
        '<div class="material"></div>' +
        '<div class="material-title"></div>' +
        '<div class="status"></div>' +
        '<div class="del"></div>' +
        '<div class="dep"></div>' +
        '<div class="reason"></div>';
      list.appendChild(row);
      rowEls.set(model.order, row);
      var rowSelect = row.querySelector('.row-select');
      rowSelect.addEventListener('change', function () { setTargetSelection(model.order, rowSelect.checked); });
      paintRow(model);
    });

    updateSelectAllState();
    updateSummary();
  }

  function paintRow(model) {
    var row = rowEls.get(model.order);
    if (!row) return;
    row.className = 'result-row ' + (model.statusClass || '');
    var rowSelect = row.querySelector('.row-select');
    if (rowSelect) {
      rowSelect.checked = model.kind === 'target' && !!model.selected;
      rowSelect.disabled = running || model.kind !== 'target';
      rowSelect.title = model.kind === 'target' ? (model.selected ? '延長対象' : '延長対象から除外') : '前提条件により処理対象外';
    }
    row.querySelector('.material').textContent = model.no;
    var titleEl = row.querySelector('.material-title');
    var fullTitle = model.title ? String(model.title) : '';
    titleEl.textContent = fullTitle || '—';
    if (fullTitle) {
      titleEl.setAttribute('title', fullTitle);
    } else {
      titleEl.removeAttribute('title');
    }
    var statusEl = row.querySelector('.status');
    var statusText = model.status || '';
    statusEl.textContent = statusText;
    if (statusText) statusEl.setAttribute('title', statusText);
    else statusEl.removeAttribute('title');

    var delEl = row.querySelector('.del');
    var delText = model.delNote && model.delNote !== '-' ? model.delNote : '—';
    delEl.textContent = delText;
    if (delText !== '—') delEl.setAttribute('title', delText);
    else delEl.removeAttribute('title');

    var depEl = row.querySelector('.dep');
    var depText = model.depNote && model.depNote !== '-' ? model.depNote : '—';
    depEl.textContent = depText;
    if (depText !== '—') depEl.setAttribute('title', depText);
    else depEl.removeAttribute('title');

    row.querySelector('.reason').textContent = model.reason || '';
  }

  function modelForOrder(order) {
    return rowModels.find(function (r) { return r.order === order; });
  }

  function updateRow(order, patch) {
    var model = modelForOrder(order);
    if (!model) return;
    Object.assign(model, patch);
    paintRow(model);
    updateSummary();
  }

  function updateMaterialDateDisplay(item, delIso, depIso) {
    var delText = delIso ? displayIso(delIso) : '-';
    var depText = depIso ? displayIso(depIso) : '-';
    var matched = false;

    rowModels.forEach(function (model) {
      var sameMaterial = !!(item && item.noKey && model.noKey && item.noKey === model.noKey);
      if (model.order !== item.order && !sameMaterial) return;
      model.delNote = delText;
      model.depNote = depText;
      paintRow(model);
      matched = true;
    });

    if (matched) updateSummary();
  }

  function updateSummary() {
    if (!currentContext || !shadow) return;
    var targetModels = getSelectedTargetModels();
    var targetsTotal = targetModels.length;
    var completed = targetModels.filter(function (r) { return r.final; }).length;
    var success = rowModels.filter(function (r) { return r.final && r.status === '成功'; }).length;
    var fail = rowModels.filter(function (r) { return r.final && /^失敗/.test(r.status); }).length;
    var exclude = rowModels.filter(function (r) { return r.kind === 'excluded'; }).length;
    var skip = rowModels.filter(function (r) {
      return r.final && r.kind !== 'excluded' && /スキップ/.test(r.status);
    }).length;
    var pct = targetsTotal ? Math.round((completed / targetsTotal) * 100) : 0;

    $('progress-bar').style.width = pct + '%';
    $('progress-text').textContent = completed + ' / ' + targetsTotal + '件 (' + pct + '%)';
    $('count-success').textContent = String(success);
    $('count-skip').textContent = String(skip);
    $('count-fail').textContent = String(fail);
    $('count-exclude').textContent = String(exclude);
  }

  function prepareFreshUi(ctx) {
    currentContext = ctx;
    launchSnapshot = makeSnapshot(ctx);
    running = false;

    createUi();
    host.style.display = '';

    var today = new Date();
    executionDateIso = isoLocal(today);
    $('delete-date').min = executionDateIso;
    $('deposit-date').min = executionDateIso;
    $('delete-date').value = '';
    $('deposit-date').value = '';
    $('deposit-date').disabled = false;
    var mode2 = shadow.querySelector('input[name="mode"][value="2"]');
    if (mode2) mode2.checked = true;

    $('screen-info').textContent = '実行画面: ' + ctx.screenDesc + ' / ' + ctx.viewDesc;

    $('config-area').style.opacity = '1';
    Array.from(shadow.querySelectorAll('#config-area input')).forEach(function (el) { el.disabled = false; });
    $('deposit-date').disabled = false;
    $('btn-x').disabled = false;
    $('btn-close').disabled = false;
    $('btn-close').style.display = '';
    $('btn-run').style.display = '';
    $('btn-run').textContent = 'ホイミ';
    $('state-title').textContent = '実行内容を確認してください';
    $('current').textContent = '';
    $('footer-note').textContent = '対象一覧と設定日を確認してから実行してください。';
    sortState = { key: null, direction: null };
    renderRows(ctx);
    applyRowSort();
    updateDetectedInfo();
    refreshPreRunMessage();
    validateConfig();
  }

  function showFresh() {
    if (running) {
      // 実行中にBlazor enhanced navigation等でhostだけDOMから外れた場合は、
      // UIを再生成せず同じhostを再接続する。これにより進捗・結果・イベント状態を保持する。
      if (host && !host.isConnected) {
        console.warn('[CV日付一括設定] 実行中のUIホストがDOMから切り離されたため再接続します。');
        (document.body || document.documentElement).appendChild(host);
      }
      if (host) host.style.display = '';
      return;
    }

    var ctx = captureContext();
    if (!ctx.ok) {
      alert(ctx.message);
      return;
    }
    prepareFreshUi(ctx);
  }

  function closeTool() {
    if (running) return;
    if (host) host.style.display = 'none';
  }

  // ===== 実行中ガード ========================================================
  function installExecutionGuard() {
    if (guardCleanup) return;

    var guardedEvents = [
      'pointerdown', 'pointerup', 'mousedown', 'mouseup', 'click', 'dblclick',
      'contextmenu', 'wheel', 'touchstart', 'touchmove', 'keydown', 'keypress',
      'keyup', 'dragstart', 'drop'
    ];

    var block = function (e) {
      // ツール自身がwebCVへ送る合成イベント(isTrusted=false)は通し、実ユーザー操作のみ遮断する。
      if (!e.isTrusted) return;
      var path = typeof e.composedPath === 'function' ? e.composedPath() : [];
      if (path.indexOf(host) !== -1) return;
      e.preventDefault();
      e.stopPropagation();
      if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
    };

    guardedEvents.forEach(function (name) {
      document.addEventListener(name, block, true);
    });

    beforeUnloadHandler = function (e) {
      if (!running) return;
      e.preventDefault();
      e.returnValue = '';
      return '';
    };
    window.addEventListener('beforeunload', beforeUnloadHandler);

    guardCleanup = function () {
      guardedEvents.forEach(function (name) {
        document.removeEventListener(name, block, true);
      });
      if (beforeUnloadHandler) {
        window.removeEventListener('beforeunload', beforeUnloadHandler);
        beforeUnloadHandler = null;
      }
      guardCleanup = null;
    };
  }

  function removeExecutionGuard() {
    if (guardCleanup) guardCleanup();
  }

  // ===== window.open フック ==================================================
  function installWindowOpenHook() {
    if (originalWindowOpen) return;
    originalWindowOpen = window.open;

    window.open = function (url, name, features) {
      if (USE_IFRAME) {
        var ifr = document.createElement('iframe');
        // display:none では内部要素の寸法が0になり可視判定が壊れるため画面外へ配置する。
        ifr.style.cssText = 'position:fixed;left:-20000px;top:0;width:1900px;height:1000px;border:0;';
        ifr.src = url;
        document.body.appendChild(ifr);
        captured = { win: ifr.contentWindow, ifr: ifr };
        return ifr.contentWindow;
      }

      var w = originalWindowOpen.call(window, url, name, features);
      if (w) captured = { win: w, ifr: null };
      return w;
    };
  }

  function restoreWindowOpen() {
    if (originalWindowOpen) {
      window.open = originalWindowOpen;
      originalWindowOpen = null;
    }
  }

  function destroyCaptured() {
    try {
      if (captured) {
        if (captured.ifr) captured.ifr.remove();
        else if (captured.win && !captured.win.closed) captured.win.close();
      }
    } catch (e) {
      // 破棄失敗は無視する。
    }
    captured = null;
  }

  // ===== 更新エンジン ========================================================
  function clickSequence(el, withDblclick) {
    var r = el.getBoundingClientRect();
    var opts = {
      bubbles: true,
      cancelable: true,
      view: window,
      clientX: r.x + r.width / 2,
      clientY: r.y + r.height / 2,
      button: 0
    };
    var reps = withDblclick ? [1, 2] : [1];

    reps.forEach(function (seq) {
      el.dispatchEvent(new PointerEvent('pointerdown', Object.assign({}, opts, { detail: seq })));
      el.dispatchEvent(new MouseEvent('mousedown', Object.assign({}, opts, { detail: seq })));
      el.dispatchEvent(new PointerEvent('pointerup', Object.assign({}, opts, { detail: seq })));
      el.dispatchEvent(new MouseEvent('mouseup', Object.assign({}, opts, { detail: seq })));
      el.dispatchEvent(new MouseEvent('click', Object.assign({}, opts, { detail: seq })));
    });

    if (withDblclick) {
      el.dispatchEvent(new MouseEvent('dblclick', Object.assign({}, opts, { detail: 2 })));
    }
  }

  function getDoc() {
    if (!captured) return null;
    return captured.ifr ? captured.ifr.contentDocument : captured.win.document;
  }

  function findDateInputByLabel(doc, label) {
    var leaf = Array.from(doc.querySelectorAll('div,span,label,td')).find(function (e) {
      return e.children.length === 0 && (e.innerText || '').trim() === label &&
        e.getBoundingClientRect().width > 0;
    });
    if (!leaf) return null;

    var p = leaf.parentElement;
    for (var k = 0; k < 4 && p; k++) {
      var inp = p.querySelector('input[type=date]');
      if (inp) return inp;
      p = p.parentElement;
    }
    return null;
  }

  function findArchiveSelect(doc) {
    var leaf = Array.from(doc.querySelectorAll('div,span,label,td')).find(function (e) {
      return e.children.length === 0 && (e.innerText || '').trim() === 'アーカイブ' &&
        e.getBoundingClientRect().width > 0;
    });
    if (!leaf) return null;

    var p = leaf.parentElement;
    for (var k = 0; k < 4 && p; k++) {
      var sel = p.querySelector('select');
      if (sel) return sel;
      p = p.parentElement;
    }
    return null;
  }

  function findUpdateButton(doc) {
    return Array.from(doc.querySelectorAll('button')).find(function (b) {
      return b.innerText.trim() === '更新' && b.getBoundingClientRect().width > 0;
    });
  }

  function setDateValue(inp, iso) {
    inp.value = iso;
    inp.dispatchEvent(new Event('input', { bubbles: true }));
    inp.dispatchEvent(new Event('change', { bubbles: true }));
  }

  function setPhase(item, text, attempt) {
    updateRow(item.order, {
      final: false,
      status: attempt > 1 ? '再試行中 (' + attempt + '/' + MAX_ATTEMPTS + ')' : '処理中',
      statusClass: 'processing',
      reason: text
    });
    $('current').textContent = '現在処理中: ' + (item.no || item.fallbackLabel) + ' / ' + text;
  }

  async function processOne(item, mode, del, dep, attempt) {
    destroyCaptured();

    setPhase(item, '素材を開く準備中', attempt);
    item.tile.scrollIntoView({ block: 'center', inline: 'nearest' });
    await sleep(300);

    setPhase(item, 'プレビューを開いています', attempt);
    if (!item.previewTrigger) {
      throw new Error('プレビュー起動要素を取得できない');
    }
    clickSequence(item.previewTrigger, true);
    await waitFor(function () { return captured; }, STEP_TIMEOUT_MS,
      'プレビューが開かない(アプリが window.open を呼ばない)');

    setPhase(item, 'プレビューを読み込んでいます', attempt);
    await waitFor(function () {
      var d = getDoc();
      if (!d) return false;
      if (d.location && d.location.pathname === '/Error') {
        throw fatalError('プレビューがエラーページに遷移した');
      }
      if (d.readyState !== 'complete' || !d.body) return false;
      return textContainsMaterialKey(d.body.innerText || d.body.textContent || '', item.noKey);
    }, STEP_TIMEOUT_MS, 'プレビュー上で対象素材番号を確認できない');

    var previewDoc = getDoc();
    var previewText = previewDoc && previewDoc.body
      ? (previewDoc.body.innerText || previewDoc.body.textContent || '') : '';
    if (!textContainsMaterialKey(previewText, item.noKey)) {
      throw new Error('プレビュー上で対象素材番号(' + item.no + ')を確認できない');
    }

    setPhase(item, '管理情報タブへ切り替えています', attempt);
    var tabAnchor = await waitFor(function () {
      var d = getDoc();
      if (!d) return null;
      return Array.from(d.querySelectorAll('a')).find(function (a) {
        return a.innerText.trim() === '管理情報';
      });
    }, STEP_TIMEOUT_MS, '管理情報タブが見つからない');
    tabAnchor.click();

    await waitFor(function () {
      var d = getDoc();
      if (!d) return false;
      var a = Array.from(d.querySelectorAll('a')).find(function (x) {
        return x.innerText.trim() === '管理情報';
      });
      if (!a || !a.classList.contains('active')) return false;
      return !!findDateInputByLabel(d, '削除日');
    }, STEP_TIMEOUT_MS, '管理情報タブへの切替が完了しない');

    setPhase(item, '現在の日付とアーカイブ設定を確認しています', attempt);
    var doc = getDoc();
    var delInp = findDateInputByLabel(doc, '削除日');
    if (!delInp) throw new Error('削除日の入力欄を特定できない');
    if (delInp.disabled) throw new Error('削除日の入力欄が無効化されている');

    var depInp = findDateInputByLabel(doc, '預入日');
    var arcSel = findArchiveSelect(doc);
    var archive = arcSel
      ? (arcSel.value === 'Target' ? '対象' : (arcSel.value === 'NotTarget' ? '対象外' : '未設定'))
      : '不明';
    var depEditable = !!depInp && !depInp.disabled;

    var curDel = delInp.value;
    var curDep = depInp ? depInp.value : '';

    // リスト表示の初期値より管理情報の実値を正とする。
    // この時点で確認できた日付へ更新し、以後エラーになっても「最後に確認できた実値」を残す。
    updateMaterialDateDisplay(item, curDel, curDep);

    // 削除日延長専用ルール:
    // - 既存削除日が空欄の素材は、削除日・預入日とも変更せず素材全体をスキップする。
    // - 指定削除日が既存削除日より前なら「前倒し」とみなし、預入日も含めて一切変更しない。
    // - 指定削除日が既存削除日と同日なら延長条件を満たす。削除日は変更せず、
    //   モード2では必要に応じて預入日のみ更新できる。
    if (!curDel) {
      await closePreview();
      return {
        status: 'スキップ',
        delNote: curDel ? displayIso(curDel) : '-',
        depNote: curDep ? displayIso(curDep) : '-',
        reason: '既存削除日が未設定のため'
      };
    }

    if (del.iso < curDel) {
      await closePreview();
      return {
        status: 'スキップ',
        delNote: displayIso(curDel),
        depNote: curDep ? displayIso(curDep) : '-',
        reason: '削除日前倒し禁止: 既存削除日(' + displayIso(curDel) + ') > 指定削除日(' + del.disp + ')'
      };
    }

    // ここまで到達した時点で「指定削除日 >= 既存削除日」= 削除日延長条件を満たす。
    // 絶対ルール: 最終状態で「削除日 > 預入日」を満たさない素材は変更しない。
    var needDel = del.iso > curDel;
    var willSetDep = mode === '2' && depEditable;
    var finalDep = willSetDep ? dep.iso : curDep;
    if (finalDep && del.iso <= finalDep) {
      await closePreview();
      return {
        status: 'スキップ',
        delNote: displayIso(curDel),
        depNote: curDep ? displayIso(curDep) : '-',
        reason: '制約違反回避: 削除日(' + del.disp + ') > 預入日(' + displayIso(finalDep) + ') を満たさないため'
      };
    }

    var needDep = willSetDep && curDep !== dep.iso;
    var depMatchesRequested = mode === '2' && curDep === dep.iso;
    var noChangeReason = '指定削除日は既存削除日と同一';
    var noChangeStatus = 'スキップ(設定済み)';

    if (mode === '2') {
      if (!depEditable && !depMatchesRequested) {
        noChangeReason += '・預入日更新スキップ(アーカイブ' + archive + ')';
        noChangeStatus = 'スキップ';
      } else if (depMatchesRequested) {
        noChangeReason += '・預入日は指定値設定済み';
      }
    }

    if (!needDel && !needDep) {
      await closePreview();
      return {
        status: noChangeStatus,
        delNote: displayIso(curDel),
        depNote: curDep ? displayIso(curDep) : '-',
        reason: noChangeReason
      };
    }

    setPhase(item, '日付を入力しています', attempt);
    if (needDel) setDateValue(delInp, del.iso);
    if (needDep) setDateValue(depInp, dep.iso);

    setPhase(item, '更新ボタンの有効化を確認しています', attempt);
    await waitFor(function () {
      var b = findUpdateButton(getDoc());
      if (b && !b.disabled) return true;

      var d2 = getDoc();
      if (!d2) return false;
      var di = findDateInputByLabel(d2, '削除日');
      if (needDel && di && !di.disabled && di.value !== del.iso) setDateValue(di, del.iso);
      var pi = findDateInputByLabel(d2, '預入日');
      if (needDep && pi && !pi.disabled && pi.value !== dep.iso) setDateValue(pi, dep.iso);
      return false;
    }, STEP_TIMEOUT_MS, '更新ボタンが有効化されない(変更がBlazorに伝わっていない)');

    setPhase(item, '更新を保存しています', attempt);
    var updateButton = findUpdateButton(getDoc());
    if (!updateButton) throw new Error('更新ボタンを特定できない');
    updateButton.click();

    await waitFor(function () {
      var b = findUpdateButton(getDoc());
      return b && b.disabled;
    }, STEP_TIMEOUT_MS, '保存完了を確認できない');

    setPhase(item, '保存後の値を検証しています', attempt);
    var dAfter = getDoc();
    var delAfter = findDateInputByLabel(dAfter, '削除日');
    var depAfter = findDateInputByLabel(dAfter, '預入日');

    // 保存後に実際に観測できた値を最終表示候補として先に反映する。
    // 想定値と不一致で失敗になっても、画面には最後に確認できた実値を残す。
    var confirmedDel = delAfter ? delAfter.value : curDel;
    var confirmedDep = depAfter ? depAfter.value : curDep;
    updateMaterialDateDisplay(item, confirmedDel, confirmedDep);

    if (!delAfter || delAfter.value !== del.iso) {
      throw new Error('保存後の削除日が想定と異なる (' + (delAfter ? delAfter.value : '不明') + ')');
    }

    if (needDep && (!depAfter || depAfter.value !== dep.iso)) {
      throw new Error('保存後の預入日が想定と異なる (' + (depAfter ? depAfter.value : '不明') + ')');
    }

    setPhase(item, 'プレビューを閉じています', attempt);
    await closePreview();

    var successReason;
    if (mode === '1') {
      successReason = needDel ? '削除日延長' : '削除日変更なし';
    } else if (!depEditable) {
      successReason = (needDel ? '削除日延長' : '削除日変更なし') +
        (depMatchesRequested
          ? '・預入日は指定値設定済み'
          : '・預入日更新スキップ(アーカイブ' + archive + ')');
    } else if (needDel && needDep) {
      successReason = '削除日延長・預入日更新';
    } else if (needDel && !needDep) {
      successReason = '削除日延長・預入日は指定値設定済み';
    } else {
      successReason = '削除日変更なし・預入日のみ更新';
    }

    return {
      status: '成功',
      delNote: confirmedDel ? displayIso(confirmedDel) : '-',
      depNote: confirmedDep ? displayIso(confirmedDep) : '-',
      reason: successReason
    };
  }

  async function closePreview() {
    var doc = getDoc();
    if (doc) {
      try {
        var btns = Array.from(doc.querySelectorAll('button')).filter(function (b) {
          return b.getBoundingClientRect().width > 0;
        });
        var upd = btns.find(function (b) { return b.innerText.trim() === '更新'; });
        var closeBtn = btns.filter(function (b) { return b.innerText.trim() === '閉じる'; })
          .find(function (b) { return upd && b.parentElement === upd.parentElement; }) ||
          btns.filter(function (b) { return b.innerText.trim() === '閉じる'; }).pop();
        if (closeBtn) closeBtn.click();
      } catch (e) {
        // 後段の破棄処理に任せる。
      }
    }

    if (captured && captured.ifr) {
      await sleep(800);
      destroyCaptured();
    } else if (captured && captured.win) {
      try {
        await waitFor(function () { return captured.win.closed; }, 8000, '閉じる');
      } catch (e) {
        destroyCaptured();
      }
      captured = null;
    }
  }

  // ===== 実行制御 ============================================================
  async function startRun() {
    if (running || !validateConfig()) return;

    var mode = getMode();
    var del = { iso: $('delete-date').value, disp: displayIso($('delete-date').value) };
    var dep = mode === '2'
      ? { iso: $('deposit-date').value, disp: displayIso($('deposit-date').value) }
      : null;
    var selectedOrders = new Set(getSelectedTargetModels().map(function (r) { return r.order; }));

    // 実行直前に画面種別・グループ・全素材分類を再取得し、起動時との差分を検査する。
    var fresh = captureContext();
    if (!fresh.ok || !snapshotsEqual(launchSnapshot, fresh.ok ? makeSnapshot(fresh) : null)) {
      $('state-title').textContent = '処理を中断しました';
      $('current').textContent = '';
      setMessage(
        '起動後に対象素材または実行条件の状態が変化しました。安全のため処理を中断しました。ツールを閉じて再実行してください。' +
        (!fresh.ok && fresh.message ? ' (' + fresh.message.replace(/\n/g, ' ') + ')' : ''),
        'error'
      );
      $('btn-run').style.display = 'none';
      $('config-area').style.opacity = '.55';
      Array.from(shadow.querySelectorAll('input')).forEach(function (el) { el.disabled = true; });
      $('footer-note').textContent = 'データは変更していません。ツールを閉じて再実行してください。';
      return;
    }

    // 最新DOM参照を処理に使う。スナップショットは同一なので対象内容は起動時と一致している。
    currentContext = fresh;
    var selectedTargets = currentContext.targets.filter(function (item) { return selectedOrders.has(item.order); });
    if (selectedTargets.length === 0 || selectedTargets.length !== selectedOrders.size) {
      $('state-title').textContent = '処理を中断しました';
      $('current').textContent = '';
      setMessage('選択した処理対象を最新画面と対応付けできませんでした。安全のため処理を中断しました。ツールを閉じて再実行してください。', 'error');
      $('btn-run').style.display = 'none';
      $('config-area').style.opacity = '.55';
      Array.from(shadow.querySelectorAll('input')).forEach(function (el) { el.disabled = true; });
      $('footer-note').textContent = 'データは変更していません。ツールを閉じて再実行してください。';
      return;
    }
    running = true;
    updateSortHeaders();
    ensureTimer();
    installExecutionGuard();

    $('btn-x').disabled = true;
    $('btn-close').disabled = true;
    $('btn-close').style.display = 'none';
    $('btn-run').disabled = true;
    $('btn-run').style.display = 'none';
    Array.from(shadow.querySelectorAll('input')).forEach(function (el) { el.disabled = true; });
    $('config-area').style.opacity = '.58';
    $('state-title').textContent = '削除日・預入日を一括設定しています';
    $('footer-note').textContent = '処理完了までこのタブを閉じたり、webCVを操作しないでください。';
    setMessage('実行中はwebCVの背後画面を操作できません。進捗と結果はこの一覧へ随時反映されます。', 'info');

    // 最新Contextでも分類結果は同一のため、行モデルのorderをそのまま利用できる。
    installWindowOpenHook();
    var fatalRunError = null;

    try {
      for (var i = 0; i < selectedTargets.length; i++) {
        var item = selectedTargets[i];
        var result = null;

        for (var attempt = 1; attempt <= MAX_ATTEMPTS; attempt++) {
          try {
            if (attempt > 1) {
              setPhase(item, '再試行の準備をしています', attempt);

              // サムネイル表示では、実績のある「別素材を1回クリックして選択状態をリセット」を維持する。
              // リスト表示では行選択リセットの効果が実証されていないため、この手順には依存せず
              // 同じpreviewTriggerへの再dblclickをそのまま再試行する。
              if (currentContext.viewMode === 'thumbnail') {
                var other = selectedTargets.find(function (t) { return t !== item; }) ||
                  currentContext.duplicates[0] || currentContext.excluded[0];
                if (other && other.previewTrigger) {
                  clickSequence(other.previewTrigger, false);
                  await sleep(700);
                }
              } else {
                await sleep(700);
              }
            }

            result = await processOne(item, mode, del, dep, attempt);
            if (attempt > 1) {
              result.reason = (result.reason ? result.reason + ' / ' : '') + 'リトライで成功';
            }
            break;
          } catch (e) {
            var msg = String((e && e.message) || e);
            console.warn('[' + (item.no || item.fallbackLabel) + '] 試行 ' + attempt + ' 失敗: ' + msg);
            var failedModel = modelForOrder(item.order);
            result = {
              status: '失敗',
              delNote: failedModel ? failedModel.delNote : '-',
              depNote: failedModel ? failedModel.depNote : '-',
              reason: msg
            };
            destroyCaptured();

            if (attempt < MAX_ATTEMPTS) {
              updateRow(item.order, {
                final: false,
                status: '1回目失敗',
                statusClass: 'processing',
                reason: msg + ' / 再試行します'
              });
            }
            await sleep(1000);
          }
        }

        var statusClass = result.status === '成功' ? 'success' :
          (result.status === '失敗' ? 'fail' : 'skip');
        updateRow(item.order, {
          final: true,
          status: result.status,
          statusClass: statusClass,
          delNote: result.delNote,
          depNote: result.depNote,
          reason: result.reason || ''
        });

        await sleep(BETWEEN_MATERIALS_MS);
      }
    } catch (e) {
      fatalRunError = e;
    } finally {
      restoreWindowOpen();
      destroyCaptured();
      finishTimer();
      running = false;
      removeExecutionGuard();
    }

    if (fatalRunError) {
      $('state-title').textContent = '処理中に予期しないエラーが発生しました';
      $('current').textContent = '';
      setMessage(String((fatalRunError && fatalRunError.message) || fatalRunError), 'error');
      $('footer-note').textContent = '一覧の状態を確認し、失敗・未完了素材は個別に確認してください。';
    } else {
      $('state-title').textContent = '一括設定が完了しました';
      $('current').textContent = '';
      setMessage('', 'info');
      $('footer-note').textContent = '結果一覧を確認してください。失敗がある場合は対象素材を個別に確認してください。';
    }

    $('btn-x').disabled = false;
    $('btn-close').disabled = false;
    $('btn-close').style.display = '';
    $('btn-run').style.display = 'none';
    applyRowSort();

    // 画面に表示している全素材をそのまま結果として保存する。
    // 予期しない中断があった場合も「処理中 / 待機中」の行を欠落させない。
    var results = rowModels.map(function (r) {
      return {
        order: r.order,
        no: r.no,
        status: r.status,
        delNote: r.delNote,
        depNote: r.depNote,
        reason: r.reason
      };
    }).sort(function (a, b) { return a.order - b.order; });

    window[RESULT_GLOBAL] = results;
    console.log('===== 削除日/預入日 一括設定 結果 =====');
    console.table(results.map(function (r) {
      return {
        素材番号: r.no,
        結果: r.status,
        削除日: r.delNote,
        預入日: r.depNote,
        備考: r.reason
      };
    }));
    updateSummary();
  }

  // ===== 公開 ============================================================== 
  window[TOOL_GLOBAL] = {
    version: TOOL_VERSION,
    show: showFresh,
    destroy: function () {
      if (running) return false;
      removeExecutionGuard();
      restoreWindowOpen();
      destroyCaptured();
      finishTimer();
      if (host) host.remove();
      host = null;
      shadow = null;
      currentContext = null;
      launchSnapshot = null;
      rowModels = [];
      rowEls.clear();
      sortState = { key: null, direction: null };
      try { delete window[TOOL_GLOBAL]; } catch (e) { window[TOOL_GLOBAL] = null; }
      return true;
    },
    get running() { return running; }
  };

  showFresh();
})();
