CXX = g++
CXXFLAGS = -O3 -static-libgcc -static-libstdc++
TARGET = LS-OptSMT

SRCS = nia_build_instance.cpp \
       call_omt.cpp \
       nia_print.cpp \
       nia_ls.cpp \
       nia_initialize.cpp

all:
	@$(CXX) $(CXXFLAGS) $(SRCS) -o $(TARGET)

clean:
	@rm -f $(TARGET)
