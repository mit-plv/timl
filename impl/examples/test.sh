set -o pipefail && make -C .. && ../main.sh --annoless annoless/stdlib.pkg annoless/test-suite.pkg && ../main.sh stdlib.pkg test-suite.pkg
