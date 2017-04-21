from ipykernel.kernelbase import Kernel
import os

class EchoKernel(Kernel):
    implementation = 'TiML'
    implementation_version = '1.0'
    language = 'no-op'
    language_version = '0.1'
    language_info = {
        'name': 'TiML',
        'mimetype': 'text/plain',
        'file_extension': '.timl',
    }
    banner = "TiML"

    def do_execute(self, code, silent, store_history=True, user_expressions=None,
                   allow_stdin=False):
        if not silent:
            tmp_file_name = '.timl-jupyter-tmp.timl'
            tmp_file = open(tmp_file_name, 'w')
            tmp_file.write(code)
            tmp_file.close()
            tmp_out_file_name = '.timl-jupyter-out-tmp.txt'
            timl = 'timl'
            cmd = "%(timl)s %(tmp_file_name)s > %(tmp_out_file_name)s" % locals()
            os.system(cmd)
            tmp_out_file = open(tmp_out_file_name)
            result = tmp_out_file.read()
            tmp_out_file.close()
            stream_content = {'name': 'stdout', 'text': result}
            self.send_response(self.iopub_socket, 'stream', stream_content)

        return {'status': 'ok',
                # The base class increments the execution count
                'execution_count': self.execution_count,
                'payload': [],
                'user_expressions': {},
               }

if __name__ == '__main__':
    from ipykernel.kernelapp import IPKernelApp
    IPKernelApp.launch_instance(kernel_class=EchoKernel)
