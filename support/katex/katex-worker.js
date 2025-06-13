#!/usr/bin/env node
const katex = require('katex');

process.stdin.setEncoding('utf8');

// An equation might be split across two chunks
// of input. If this happens, we store the first
// part of the equation in `partialEquation`.
let partialJob = "";

process.stdin.on('data', (chunk) => {
    // See [HACK: File Separator Control Characters] for
    // explanation of '\x1C'.
    const jobs = chunk.split('\x1C');
    jobs[0] = partialJob + jobs[0];
    partialJob = jobs.pop() || "";
    process.stderr.write(JSON.stringify(jobs));
    jobs.forEach((job) => {
        job = JSON.parse(job);
        try {
            const html = katex.renderToString(job.equation, job.options);
            process.stdout.write("Ok:" + html + '\x1C');
        } catch(e) {
	    process.stdout.write("Katex compilation failed for:\n" + job.equation + "\nError:\n" + e.message + '\^');
        }
    });
});

process.stdin.on('end', (chunk) => {
    console.error("Input ended with non-terminated equation:\n", partialEquation);
});
