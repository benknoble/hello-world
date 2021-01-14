import subprocess
import shlex

import flask

RACKET = r"""
(require racket/sandbox)

(parameterize ([sandbox-output 'string])
  (let ([e (make-evaluator 'racket/base '(begin %s))])
    (display (get-output e))))

(exit)
"""


def run_racket(code):
    sandbox_code = shlex.quote(RACKET % code)
    sandbox = shlex.split(f"racket -qe {sandbox_code}")
    proc = subprocess.run(sandbox, text=True, capture_output=True, timeout=1)
    return proc


def format_output(proc):
    return f"output:\n{proc.stdout}\nerror:\n{proc.stderr}"


def create_app():
    app = flask.Flask(__name__)

    index_routes = dict(
        GET=lambda: flask.render_template("index.html"),
        POST=lambda: flask.render_template(
            "index.html",
            output=format_output(run_racket(flask.request.form["code"])),
        ),
    )

    @app.route("/", methods=["GET", "POST"])
    def hello_world():
        return index_routes[flask.request.method]()

    return app
