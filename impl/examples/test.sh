set -o pipefail && make -C .. && xargs -a suite.txt ../main.sh
