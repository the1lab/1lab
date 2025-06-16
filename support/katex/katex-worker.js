const { Transform } = require('node:stream');
const { Buffer } = require('node:buffer');
const katex = require('katex');

// Stream transformer that consumes JSON-encoded job
// requests delimited by null bytes, and writes
// HTML responses that are similarly delimited by
// null bytes.
// See [NOTE: Delimiting KaTeX jobs] for more information.
const katexHtml = new Transform({
    construct(done) {
        this.trailingChunk = Buffer.alloc(0);
        done();
    },

    transform(chunk, _encoding, done) {
        chunk = Buffer.concat([this.trailingChunk, chunk]);
        let start = 0;
        let end = chunk.indexOf(0x00, start);;
        while (end !== -1) {
            const job = JSON.parse(chunk.toString('utf8', start, end));
            const html = katex.renderToString(job.equation, job.options);
	    // Allocate an extra byte for our buffer for the null terminator.
	    // We can use `unsafeAlloc` here, as we are going to be overwritting
	    // all of the contents ourselves.
	    const nbytes = Buffer.byteLength(html);
	    const output = Buffer.allocUnsafe(nbytes + 1);
	    output.write(html);
	    output[html.length] = 0x00;
            this.push(output);
            start = end + 1;
            end = chunk.indexOf(0x00, start);
        }
        // Handle any incomplete chunks.
        if (start < chunk.length) {
            this.trailingChunk = chunk.subarray(start);
        } else {
	    this.trailingChunk = Buffer.alloc(0);
	}
        done();
    },

    flush(done) {
	if (this.trailingChunk.length != 0) {
	    done("KaTeX worker closing with partially written job: " + trailingChunk.toString());
	} else {
	    done();
	}
    }
});

process.stdin.pipe(katexHtml).pipe(process.stdout);
