CXX = g++
CXXFLAGS = -O3 -static-libgcc -static-libstdc++
TARGET = LS-OptSMT

SRCS = nia_build_instance.cpp \
       call.cpp \
       nia_print.cpp \
       nia_ls_nnf.cpp \
       nia_initialize_nnf.cpp

all:
	@$(CXX) $(CXXFLAGS) $(SRCS) -o $(TARGET)

clean:
	@rm -f $(TARGET)
