from verifier import verify_code
from print_z3 import z3_to_latex
from flask import Flask, request, jsonify, send_from_directory

app = Flask(__name__)

@app.route('/')
def index():
    return send_from_directory('.', 'index.html')

# /verify route
@app.route('/verify', methods=['POST'])
def verify_server():
    data = request.get_json()
    code = data['code']
    pre_condition = data['preCondition']
    post_condition = data['postCondition']
    verification_type = data['type']

    ret_value = verify_code(code, pre_condition, post_condition, verification_type)
    return jsonify({
    'success': ret_value[0],
    'formula': str(ret_value[1]) if "ForAll" in str(ret_value[1]) else "\[" + z3_to_latex(ret_value[1]) + "\]",
    'model': None if ret_value[2] is None else "\(" + str(ret_value[2]) + "\)",
    'message': ret_value[3]
  }
)

if __name__ == "__main__":
    app.run(debug=True)