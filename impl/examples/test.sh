set -o pipefail && make -C .. && cat suite.txt | xargs ../main.sh
