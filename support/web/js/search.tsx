import { JSX, type Content } from "./lib/jsx";
import { type MatchedSpan, type PromptItem, highlight, spanMaybe } from "./prompt/items";
import { InThisPage, Miscellanea } from "./prompt/sections";

type SearchItem = {
  idIdent: string,
  idAnchor: string,
  idType: string | null,
  idDefines: string[] | null,
};

const makeSearch = (e: SearchItem, thisp: boolean): PromptItem => {
  const sel: string[] = [ e.idIdent, ...e.idDefines ?? [] ];
  const original = e.idIdent;

  const desc: Content[] = [];
  if (e.idType) {
    desc.push(<p class="search-type sourceCode">{e.idType}</p>)
  };

  return {
    selectors: sel,
    activate: () => {
      window.location.href = e.idAnchor;
      return 'close';
    },
    onlySearch: !thisp && (`${e.idIdent}.html` !== e.idAnchor),
    priority: e.idType ? -1 : 1,

    render(key: string, matched?: MatchedSpan) {
      let title;
      if (original === key) {
        title = highlight(original, matched)
      } else {
        title = <span class="search-nontrivial-key">
          <span class="search-original-name">{original}</span>
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
        ...desc
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
    entries.filter((e: SearchItem) => !e.idIdent.startsWith(".")).forEach((e: SearchItem) => {
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
