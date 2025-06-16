#!/usr/bin/env node
const katex = require('katex');

process.stdin.setEncoding('utf8');

// An equation might be split across two chunks
// of input. If this happens, we store the first
// part of the equation in `partialJob`.
let partialJob = "";

process.stdin.on('data', (chunk) => {
    // See [HACK: File Separator Control Characters] for
    // explanation of '\x1C'.
    const jobs = chunk.split('\x1C');
    jobs[0] = partialJob + jobs[0];
    partialJob = jobs.pop() || "";
    jobs.forEach((job) => {
	// Instead of trying to catch errors in node and re-report them back
	// to the haskell side, we take a more laissez-faire approach and
	// just let the node process die.
        job = JSON.parse(job);
        const html = katex.renderToString(job.equation, job.options);
        process.stdout.write(html + '\x1C');
    });
});

process.stdin.on('end', () => {
    if (partialJob) {
	console.error("Input ended with non-terminated equation:\n", partialJob);
    }
});
