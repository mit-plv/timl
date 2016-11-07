set -o pipefail && make && ./main.sh --annoless examples/annoless/stdlib.pkg examples/annoless/test-suite.pkg && ./main.sh examples/stdlib.pkg examples/test-suite.pkg
