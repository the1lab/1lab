import { refreshLinks } from './highlight-hover';
import { JSX } from './lib/jsx';
import { justifiedSetting, serifFontSetting } from './lib/settings';

interface Sidenote {
  // The actual sidenote element
  content: HTMLDivElement;

  // Pair of elements for measuring baseline skip in the sidenote
  // context
  highMark: Element;
  lowMark:  Element;

  // Element with which we should align the baseline
  target: Element;

  // Enclosing details element, if one exists
  blocker?: HTMLDetailsElement;

  // Last vertical position, if one exists
  lastTop?: number;
};

function getSidenotes(): Sidenote[] {
  const notes: Sidenote[] = [];

  document.querySelectorAll("a.footnote-ref[href]").forEach((ref) => {
    if (!(ref instanceof HTMLAnchorElement)) return;
    const id = Number.parseInt(ref.hash.slice(3));
    if (isNaN(id)) return;

    const parent = document.getElementById(ref.hash.slice(1));
    if (!(parent instanceof HTMLLIElement)) return;

    const
      content  = <div class="sidenote" /> as HTMLDivElement,
      lowMark  = <span class="sidenote-baseline-mark" />,
      highMark = <span class="sidenote-number">{lowMark}{id}</span>,
      children = Array.from(parent.children).map(e => e.cloneNode(true));

    children.unshift(highMark);
    content.replaceChildren(...children);

    let
      blocker: HTMLDetailsElement | undefined = ref.closest("details") ?? undefined,
      summary = ref.closest("summary");

    const target = <span class="sidenote-baseline-mark" />;
    ref.insertAdjacentElement('afterbegin', target);

    if (summary) { blocker = undefined; }
    if (blocker && !blocker.open) { content.style.display = 'none'; }

    notes.push({ content, highMark, lowMark, target, blocker });
  });

  return notes;
}

document.addEventListener("DOMContentLoaded", () => {
  const parent = document.getElementById("sidenote-container");
  if (!(parent instanceof HTMLElement)) return;

  const notes = getSidenotes();
  console.log(notes);

  parent.replaceChildren(...notes.map(n => n.content));
  refreshLinks();

  let shown = false;

  const reposition = () => {
    if (notes.length < 1) return;

    console.log(`Repositioning ${notes.length} sidenotes`);

    // Start of the next free space to put a sidenote into.
    let nextFree = -1;

    // Since everything is done based on screen coordinates, we need to
    // know how far off the viewport the top of the sidenote container
    // is.
    const offset = parent.getBoundingClientRect().top;

    notes.forEach(note => {
      const { content, highMark, lowMark, target, blocker, lastTop } = note;

      // If the note is in a <details> and that <details> is closed,
      // skip laying out the note, and make sure to hide it.
      if (blocker && !blocker.open) {
        content.style.display = 'none';
        return;
      } else if (blocker) {
        content.style.display = 'block';
      }

      // Aligning the side notes is very finnicky, at least when there's
      // enough space.
      //
      // The typographically sound way to do this is to align the
      // *baselines* of the line containing the reference and the first
      // line of the sidenote. Problem: There is no easy way to get the
      // text baseline of an element.
      //
      // The solution: fiddling with numbers. We store
      //
      //   * tgtBaseline - the vertical position of the baseline we want
      //   to align to
      //   * noteLineTop  - the top position of a line in the sidenote text
      //   * noteLineBase - the baseline of that same line.
      //
      // From this, we can calculate noteLineSkip, which measures how
      // much vertical space is between the stop of a <span> and the
      // baseline of the text contained in that span.
      // Starting at the tgtBaseLine and moving *up* noteLineBase px, we
      // can calculate precisely *where the sidenote should start* to
      // align the baselines.

      const
        tgtBaseline = target.getBoundingClientRect().top,

        noteLineTop  = highMark.getBoundingClientRect().top,
        noteLineBase = lowMark.getBoundingClientRect().top,

        // The baseline is *further* in the page so it is *greater* than
        // the top of the line.
        noteLineSkip = noteLineBase - noteLineTop,

        // However, it might be the case that there's already a note
        // where we want. The positioning in that case is very simple:
        // we take whatever is furthest down of [the position we
        // calculated] and [the line after the previous note].

        wanted = tgtBaseline - noteLineSkip - offset,
        actual = Math.max(wanted, nextFree);

      if (lastTop != actual) {
        note.lastTop = actual;
        content.style.top = `${actual}px`;
      }

      const height = content.getBoundingClientRect().height;
      nextFree = actual + height + noteLineSkip * 1.5;
    });

    // The sidenote container is specified as visibility: hidden in the
    // template. This is so we can reposition the reposition the
    // sidenotes without them flashing onto the screen in the top-right
    // corner on the first frame. The first time we do a reflow, we
    // display the container.
    if (!shown) {
      shown = true;
      parent.style.visibility = 'visible';
    }
  }

  // We can check whether the page is too narrow to contain the
  // sidenotes by checking whether the sidenote-container has a width.
  // If the page is too narrow, the sidenotes will get disappeared at
  // the CSS level, so doing the reflows wouldn't be an *issue*; it
  // would just be wasteful.
  const isNarrow = () => {
    return parent.getBoundingClientRect().width == 0;
  }

  const reflow = () => {
    if (!isNarrow()) window.requestAnimationFrame(reposition);
  };

  // Wait for the fonts to finish loading before doing the first reflow.
  //
  // This means that, on a slower connection (and fresh cache), the
  // sidenotes will pop in *after* the page has been laid out the first
  // time (with the incorrect font). The alternative is reflowing
  // *before* we know the final font metrics, in which case the
  // sidenotes will have to wiggle slightly to get into position.
  document.fonts.addEventListener("loadingdone", () => {
    reflow();

    window.addEventListener("resize", reflow);

    // Reflowing the entire sidenote container when a <details> opens is a
    // *slight* over-approximation (ha), but it does work.
    document.querySelectorAll("details").forEach(d =>
      d.addEventListener("toggle", reflow));

    // Make sure that our layout-affecting settings cause the sidenotes
    // to be reflowed.
    serifFontSetting.onChange(reflow);
    justifiedSetting.onChange(reflow);
  });
});
