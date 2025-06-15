cmake_minimum_required(VERSION 3.10)

project(FlatzincConverter VERSION 1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(PARSER_FILE ${CMAKE_SOURCE_DIR}/parser_gen/parser.ypp)
set(PARSER_SOURCE ${CMAKE_SOURCE_DIR}/src/parser.cpp)
set(PARSER_HEADER ${CMAKE_SOURCE_DIR}/includes/parser.hpp)

set(LEXER_FILE ${CMAKE_SOURCE_DIR}/parser_gen/lexer.lpp)
set(LEXER_OUTPUT ${CMAKE_SOURCE_DIR}/src/lexer.cpp)

find_program(BISON_EXECUTABLE bison)

if(NOT BISON_EXECUTABLE)
    message(FATAL_ERROR "bison not found")
endif()

find_program(FLEX_EXECUTABLE flex)

if(NOT FLEX_EXECUTABLE)
    message(FATAL_ERROR "flex not found")
endif()

# set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -g -O1")
# set(CMAKE_LINKER_FLAGS "${CMAKE_LINKER_FLAGS} -fsanitize=address")


add_custom_command(
    OUTPUT ${PARSER_SOURCE}
    OUTPUT ${PARSER_HEADER}
    COMMAND ${BISON_EXECUTABLE} -d -o ${PARSER_SOURCE} ${PARSER_FILE}
    DEPENDS ${PARSER_FILE}
)

add_custom_command(
    OUTPUT ${LEXER_OUTPUT}
    COMMAND ${FLEX_EXECUTABLE} -o ${LEXER_OUTPUT} ${LEXER_FILE}
    DEPENDS ${LEXER_FILE}
)

add_custom_target(
    generate_parser ALL
    DEPENDS ${PARSER_SOURCE}
    DEPENDS ${PARSER_HEADER}
)

add_custom_target(
    generate_lexer ALL
    DEPENDS ${LEXER_OUTPUT}
)

set(SOURCES
    src/main.cpp
    ${PARSER_SOURCE}
    src/encoder.cpp
    ${LEXER_OUTPUT} 
)

set(HEADERS
    ${PARSER_HEADER}
    includes/encoder.hpp
)

# Define executable target
add_executable(flatzinc_to_sat ${SOURCES})

# Make sure flatzinc_to_sat depends on the generate_lexer target
add_dependencies(generate_lexer generate_parser)
add_dependencies(flatzinc_to_sat generate_lexer)

target_include_directories(flatzinc_to_sat PRIVATE ${CMAKE_SOURCE_DIR}/includes)

# Ensure compilation options are set
target_compile_options(flatzinc_to_sat PRIVATE -Wall -g)
