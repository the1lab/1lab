import * as d3 from "d3";
import { JSX } from './lib/jsx';

type Node = {
  // The identifier for this node
  id: string,
  // The "section" for this node (determines the colour and the gravity)
  section?: string,
  // The radius of this node
  radius: number,
  colour?: string,
  saved?: string,
  fx?: number,
  fy?: number,
  x?: number,
  y?: number,
  hover?: boolean
};

type Edge = {
  source: Node,
  target: Node,
  isGravity?: boolean,
  primary?: boolean,
};

const neighbourCache: Record<string, any> = {};

function neighbours<NodeT extends Node | string>(node: NodeT, links: (NodeT extends string ? string : Edge)[]): Set<NodeT extends string ? string : Node> {
  const cacheKey: string = typeof node === 'string' ? node : node.id;
  if (neighbourCache[cacheKey]) {
    return neighbourCache[cacheKey];
  }

  // Cursed ass function tbh. The type inference works at the use sites
  // but not really here.
  const nbh = new Set<NodeT extends string ? string : Node>();
  for (let l0 of links) {
    if (typeof node === 'string') {
      const link: string[] = l0 as unknown as string[];
      if (link[0] === node) {
        nbh.add(link[1] as (NodeT extends string ? string : Node));
      } else if (link[1] === node) {
        nbh.add(link[0] as (NodeT extends string ? string : Node));
      }
    } else {
      const link: Edge = l0 as unknown as Edge;
      if (link.source === node) {
        nbh.add(link.target as (NodeT extends string ? string : Node));
      } else if (link.target === node) {
        nbh.add(link.source as (NodeT extends string ? string : Node));
      }
    }
  }
  neighbourCache[cacheKey] = nbh;
  return nbh;
}

const page = (() => {
  if (window.location.pathname === "/") {
    return "index.html"
  } else {
    return window.location.pathname.slice(1).replace(".html", "");
  }
})();

function nbhoodSubgraph(node: string, links: [string]): { nodes: Node[], edges: Edge[] } {
  const nodes = neighbours(node, links).add(node);
  const edges = [];
  const nodeMap: Record<string, Node> = {};

  const nodeEls = Array(...nodes).map(x => ({
      id: x,
      radius: x === page ? 15 : 10,
    }))

  for (const node of nodeEls) {
    nodeMap[node.id] = node;
  }

  for (const link of links) {
    const source = nodeMap[link[0]];
    const target = nodeMap[link[1]];
    if (source !== undefined && target !== undefined) {
      edges.push({
        source: source,
        target: target,
        primary: (link[0] === node || link[1] === node)
      });
    }
  }

  return {
    nodes: nodeEls,
    edges: edges
  };
}

// Compute a hue based on the string's SHA-2 hash. Overkill? Yeah,
// maybe.
const stringHue = (message: string) => {
  let i = 0;
  for (const c of message) {
    i += i * 31 + c.charCodeAt(0)
  }
  return i % 359;
}

const hsvToCss = (h: number, s : number, v : number) => {
  const f = (n : number, k = (n + h / 60) % 6) => v - v * s * Math.max(Math.min(k, 4 - k, 1), 0);
  const col = [f(5), f(3), f(1)].map(x => x * 255 | 0).join(', ')
  return "rgb(" + col + ")";
}

const makeColours = (arr: Node[]) => {
  // Populate the section and colour for each node.
  for (const x of arr) {
    const sections = x.id.split('.')
    x.section = sections.slice(0, 2).join(',');

    const hue = stringHue(x.section);
    x.colour = hsvToCss(hue, 0.5, 0.83);
  }
}

function render(nodes: d3.Selection<SVGCircleElement | d3.BaseType, Node, any, any>,
  lines: d3.Selection<SVGLineElement | d3.BaseType, Edge, any, any>,
  labels: d3.Selection<SVGGElement | d3.BaseType, Node, any, any>): () => void {
  return () => {
    // Re-position the nodes
    nodes
      .attr('cx', d => d.x as number)
      .attr('cy', d => d.y as number)
      .attr('fill', d => d.colour as string);

    lines
      // Re-position the edges
      .attr("x1", d => d.source.x as number)
      .attr("y1", d => d.source.y as number)
      .attr("x2", d => d.target.x as number)
      .attr("y2", d => d.target.y as number)
      // Control edge visibility:
      .attr("visibility", d => {
        if (d.isGravity) return 'hidden'; // Gravity is never shown

        // Show edges to/from a hovered node, and always show primary
        // edges
        if (d.primary || d.source.hover || d.target.hover) {
          return 'visible';
        }
        return 'hidden';
      })
      .attr("stroke", (d) => {
        // Change edge colour depending on the endpoints being hovered or
        // not.
        if (d.source.hover) { return d.source.colour as string; }
        if (d.target.hover) { return d.target.colour as string; }
        return 'var(--depgraph-edge)';
      });

    labels
      .attr('transform', d => d === undefined ? "" : `translate(${d.x as number + d.radius}, ${d.y as number - 5})`)
      .attr('visibility', d => {
        if (d.id === page || d.hover) {
          return 'visible';
        }
        return 'hidden';
      });
  }
};

const clamp = (x: number, lo: number, hi: number) =>
  x < lo ? lo : x > hi ? hi : x;

const resize = (sim: d3.Simulation<Node, Edge>) => {
  let last_width: number;
  const gravity = d3.forceCenter();
  sim.force('center', gravity);
  const svgEl = document.querySelector("aside#toc svg");
  if (!svgEl) return;

  // This observer watches for changes in the SVG size box and
  // re-computes the coordinates of the centering force.
  return new ResizeObserver(entries => {
    for (const _entry of entries) {
      const box = svgEl.getBoundingClientRect();
      const width = box.width, height = box.height;

      if (last_width === width) { return; }
      last_width = width;

      gravity.x(width / 2).y(height / 2);
      (sim as any)['width'] = width;
      (sim as any)['height'] = height;
      sim.alpha(1).restart();
    }
  });
};

function navigateTo<T>(_ev: T, d: Node) {
  window.location.pathname = `/${d.id}.html`;
};

const modal = (close = () => { }) => {
  if (Array.from(document.querySelectorAll("div.modal.open")).length >= 1) {
    return;
  }

  const svg = document.querySelector("aside#toc svg");
  if (!svg) return;

  // Create the open modal dialog box. This is just the backing
  // background!
  const dialog = <div class="modal open">
    <div class="modal-contents">
      <h3>Module dependency graph for {page}</h3>
      (Click outside the dialog to dismiss, double click on a node to navigate there)
      { // This element is stolen from the sidebar.
        svg
      }
    </div>
  </div>;

  const parent = document.querySelector("aside#toc > div#toc-container");
  if (!parent) return;

  dialog.addEventListener("click", (ev) => {
    // On close, re-parent the SVG to the sidebar
    if (ev.target === dialog) {
      parent.appendChild(svg);
      dialog.remove();
      close();
    }
  });

  document.body.appendChild(dialog);
};

document.addEventListener('DOMContentLoaded', async () => {
  const data = (await fetch("static/links.json").then(r => r.json())).slice(0, -1);
  const { nodes, edges } = nbhoodSubgraph(page, data);
  makeColours(nodes);

  // If there's no graph for this page, we don't append a SVG or
  // anything.
  if (edges.length <= 0) return;

  // We add a "gravity" link between each pair of nodes in the same
  // section to make "connected components" (not actually --- just
  // modules in the same section) cluster up.
  for (const n1 of nodes) {
    for (const n2 of nodes) {
      // XXX: Don't add gravity links between the primary and its orbits
      if (n1.section === n2.section && n1.id !== page && n2.id !== page) {
        edges.push({
          source: n1,
          target: n2,
          isGravity: true
        });
      }
    }
  }

  const nodesById: Record<string, Node> = {};

  // Force rendering simulation.
  const sim = d3.forceSimulation<Node>(nodes)
    // Repellent force. Nodes in the simulation VERY STRONGLY repel
    // eachother.
    .force('charge', d3.forceManyBody<Node>().strength(d => d.id === page ? -500 : -200))
    // Link force. Links are edges from the graph /or/ the "gravity"
    // edges we added above.
    .force('link', d3.forceLink<Node, Edge>(edges)
      .id(d => {
        // We take this opportunity to populate the nodesById map since
        // d3js calls this function for every node, exactly once, with
        // the right reference (so we can use the nodesById map to
        // modify the graph in-memory).
        nodesById[d.id] = d;
        return d.id;
      })
      .strength(d => {
        // Gravity links are stronger than other types of links. This
        // makes nodes with the same colour "cluster up".
        if (d.isGravity) return 0.5;
        return 0.3;
      })
      .distance(d => {
        if (d.isGravity) return 30;
        if (d.source.section === d.target.section) return 30;
        return 80;
      }))
    .force('collision', d3.forceCollide<Node>().radius(d => d.radius));

  // Allocate new zoom behaviour
  const zoom = d3.zoom<SVGSVGElement, unknown>().scaleExtent([0.5, 4]);

  const container = document.querySelector("aside#toc > div#toc-container");
  if (!container) return;
  const ruler = container.appendChild(document.createElement("hr"));

  // Create the SVG element and add a <g>roup for the zoom
  // transformation.
  const svgRoot = d3
    .select(container)
    .append('svg')
    .call(zoom);
  const svg = svgRoot.append('g');

  zoom.on('zoom', ({ transform }) => {
    svg.attr('transform', transform.toString());
  });

  // Draw the edges
  const lines = svg.selectAll('line')
    .data(edges)
    .join('line')
    .attr('stroke', 'var(--depgraph-edge)');

  // Draw the circles representing the nodes. At this point, we have
  // already populated each nodes' colour, section and radius.
  const circles: d3.Selection<SVGCircleElement | d3.BaseType, Node, any, any> =
    svg.selectAll('circle')
      .data(nodes)
      .join('circle')
      .attr('r', d => d.radius)
      .attr('fill', d => d.colour ?? "#fff");

  // Draw the label containers (this is a group that gets translated
  // into place). This is what is actually controlled by the render
  // callback: the text elements keep their position fixed (relative to
  // the <g>roups, which are translated).
  const labels =
    svg.selectAll('g')
      .data(nodes)
      .join('g');

  // Append to each group the label and the white backing for it.
  labels
    .append('text')
    .text(d => d.id)
    .attr('fill', 'var(--text-fg)')
    .clone(true).lower()
    .attr('fill', 'var(--text-fg)')
    .attr('stroke', 'var(--text-bg)')
    .attr('stroke-width', 2);

  const renderCallback = render(circles, lines, labels);
  (window as any)['renderCallback'] = renderCallback;
  (window as any)['edges'] = edges;
  sim.on('tick', renderCallback);

  // Create the resize observer to automatically change the centering
  // force when the SVG size changes (e.g. when the window is resized or
  // the modal is maximised).
  const observer = resize(sim)
  if (observer)
    observer.observe(document.querySelector("aside#toc svg")!);

  const drag = d3.drag<any, Node>().on("start", (_, d) => {
    d.fx = d.x;
    d.fy = d.y;
  }).on("drag", (event, d) => {
    d.fx = clamp(event.x, 0, (sim as any)['width']);
    d.fy = clamp(event.y, 0, (sim as any)['height']);
    sim.alpha(1).restart();
  });
  circles.call(drag);

  const onHighlight = (d: Node, on: boolean) => {
    d.hover = on;
    if (on) {
      if (d.id !== page) {
        for (const n of neighbours(d, edges)) {
          n.saved = n.colour;
          n.colour = d.colour;
        }
      }
    } else {
      for (const n of neighbours(d, edges)) {
        if (n.saved !== undefined) {
          n.colour = n.saved;
          delete n.saved;
        }
      }
    }
    renderCallback();
  }

  // Toggle visibility of the label on hover.
  circles
    .on('mouseenter', (_, d) => document.dispatchEvent(new CustomEvent('highlight', { detail: { link: d, on: true } })))
    .on('mouseleave', (_, d) => document.dispatchEvent(new CustomEvent('highlight', { detail: { link: d, on: false } })))

  // Make sure that hovering on the label keeps it shown, otherwise
  // hovering your cursor between the circle and the label causes the
  // label to flash rapidly
  labels
    .on('mouseenter', (_, d) => document.dispatchEvent(new CustomEvent('highlight', { detail: { link: d, on: true } })))
    .on('mouseleave', (_, d) => document.dispatchEvent(new CustomEvent('highlight', { detail: { link: d, on: false } })))

  // Install hover handlers for activating nodes on hovering their
  // corresponding links in the body text
  document.addEventListener('highlight', (({ detail: { link, on } }: CustomEvent) => {
    if (link instanceof HTMLAnchorElement) {
      const id = link.pathname.slice(1).replace(".html", "");
      if (nodesById[id])
        onHighlight(nodesById[id], on);
    } else {
      onHighlight(link, on);
    }
  }) as EventListener)

  // Navigate to on double click
  circles.on("dblclick", navigateTo);
  labels.on("dblclick", navigateTo);

  let addExpand: () => void;
  const reset = () => {
    // Reset zoom level
    svgRoot.transition().duration(750).call(zoom.transform, d3.zoomIdentity);
    // Clear all forced coordinates
    for (const n of nodes) {
      n.fx = undefined;
      n.fy = undefined;
    }
    // Re-center
    sim.alpha(1).restart();
  }

  addExpand = () => {
    ruler.style.display = "block";

    const expand = <button style="display: inline-block">
      Maximise network
    </button>

    expand.addEventListener("click", () => {
      ruler.style.display = "none";
      expand.remove();
      modal(addExpand);
      reset();
    });

    reset();
    container.appendChild(expand);
  };

  addExpand();
});
