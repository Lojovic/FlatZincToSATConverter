cmake_minimum_required(VERSION 3.10)

project(FlatzincConverter VERSION 1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(SOURCES
    src/main.cpp
    src/Tokenizer.cpp
    src/Parser.cpp
    src/Encoder.cpp
)

set(HEADERS
    includes/Tokenizer.h
    includes/Parser.h
    includes/Encoder.h
)

add_executable(flatzinc_to_sat ${SOURCES})

target_include_directories(flatzinc_to_sat PRIVATE ${CMAKE_SOURCE_DIR}/includes)

target_compile_options(flatzinc_to_sat PRIVATE -Wall)


