from verifier import verify_code
from global_variables import loops
from flask import Flask, request, jsonify, send_from_directory

app = Flask(__name__)

#Serve index.html from the current directory
@app.route('/')
def index():
    return send_from_directory('.', 'index.html')  # '.' refers to the current directory

# Verification route
@app.route('/verify', methods=['POST'])
def verify_server():
    data = request.get_json()
    code = data['code']
    pre_condition = data['preCondition']
    post_condition = data['postCondition']

    # Call your verification logic here (e.g., verify_code function)
    ret_value = verify_code(code, pre_condition, post_condition)
    return jsonify({
    'success': ret_value[0],
    'formula': str(ret_value[1]),
    'model': None if ret_value[2] is None else str(ret_value[2]),
    'loop_free': not loops
  }
    )

if __name__ == "__main__":
    app.run(debug=True)