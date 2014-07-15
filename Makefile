all : clors

clors: clors.cpp
	clang++ -ggdb -march=native -O3 -flto -std=c++11 -o clors clors.cpp

