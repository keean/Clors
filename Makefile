all : clors

debug: CFLAGS+="-DDEBUG"
debug: all

clors: clors.cpp
	clang++ ${CFLAGS} -ggdb -march=native -O3 -flto -std=c++11 -o clors clors.cpp

clean:
	rm -f test clors
