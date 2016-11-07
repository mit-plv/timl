set -o pipefail && make mlton && ./main.sh --annoless examples/annoless/stdlib.pkg examples/annoless/test-suite.pkg && ./main examples/stdlib.pkg examples/test-suite.pkg
