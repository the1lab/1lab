import { JSX, type Content } from "./lib/jsx";
import { type MatchedSpan, type PromptItem, highlight, spanMaybe } from "./prompt/items";
import { InThisPage, Miscellanea } from "./prompt/sections";

type SearchItem = {
  idIdent: string,
  idAnchor: string,
  idType: string | null,
  idDefines: string[] | null,
};

const showSearchItem = (e: SearchItem) => {
  const
    parts          = e.idIdent.split(" > "),
    isHidden       = e.idIdent.startsWith("."),
    isSection      = parts.length > 1,
    isBibliography = parts[parts.length - 1].startsWith("ref")
    ;
  return !isHidden && (!isSection || !isBibliography);
};

const makeSearch = (e: SearchItem, thisp: boolean): PromptItem => {
  const parts = e.idIdent.split(" > ");

  let selector = e.idIdent;
  if (!e.idType && parts.length > 1) {
    selector = parts[parts.length - 1];
  }

  const sel: string[] = [ selector, e.idIdent, ...e.idDefines ?? [] ];

  let desc: Content | undefined;
  if (e.idType) {
    desc = <span class="search-type sourceCode">{e.idType}</span>;
  } else if (parts.length > 1) {
    desc = <span class="search-desc">{parts.slice(0, -1).join(" > ")}</span>;
  };

  const clickTarget = <a href={e.idAnchor} />;

  return {
    selectors: sel,
    activate: (aux) => {
      if (aux) {
        clickTarget.dispatchEvent(new MouseEvent('click', {
          ctrlKey: true, // for Windows or Linux
          metaKey: true, // for MacOS
        }));
        return 'keep';
      } else {
        window.location.href = e.idAnchor;
        return 'close';
      }
    },

    onlySearch: !thisp && (`${e.idIdent}.html` !== e.idAnchor),
    priority: e.idType ? -1 : 1,

    render(key: string, matched?: MatchedSpan) {
      let title;
      if (selector === key) {
        title = highlight(selector, matched);
      } else if (e.idIdent === key && parts.length > 1) {
        title = <span>{selector}</span>;
        desc = <span class="search-desc">
          {highlight(key, matched)}
        </span>;
      } else {
        title = <span class="search-nontrivial-key">
          <span class="search-original-name">{selector}</span>
          <span class="search-match-key">
            {highlight(key, matched)}
          </span>
        </span>
      };

      return [
        <h3 class={`search-header ${e.idType && "search-identifier"}`}>
          {spanMaybe(title)}
          <span class="search-module">{e.idAnchor.replace(/.html(#.+)?$/, "")}</span>
        </h3>,
        desc
      ];
    },
  };
};

let path = window.location.pathname.split('/');
let page = path[path.length - 1];
if (page.length === 0) { page = "index.html"; }

let thisp = 0, done = false;

fetch("static/search.json")
  .then(r => r.json())
  .then(entries => {
    entries.filter(showSearchItem).forEach((e: SearchItem) => {
      if (e.idAnchor.startsWith(page)) {
        if (e.idAnchor !== page) {
          InThisPage.pushPromptItems(makeSearch(e, true));
        }
      } else {
        Miscellanea.pushPromptItems(makeSearch(e, false));
      }
      if (!done && (done = thisp++ > 32)) document.dispatchEvent(new Event("searchready"));
    });
  })
  .catch(e => {
    console.error("Failed to load search index", e);
  });
