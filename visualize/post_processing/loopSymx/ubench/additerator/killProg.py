import multiprocessing
import time

# Your foo function
def foo(n):
    for i in range(10000 * n):
        print "Tick"
        time.sleep(1)

if __name__ == '__main__':
    # Start foo as a process
    p = multiprocessing.Process(target=foo, name="Foo", args=(10,))
    p.start()

    # Wait 10 seconds for foo
    time.sleep(10)

    # Terminate foo
    p.terminate()

    # Cleanup
    p.join()
