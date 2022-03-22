--------------------------- MODULE MC -----------------------------------------
\* an instance of BinSearch with all parameters fixed

\* fix 8 bits
INT_WIDTH == 8
\* the input sequence to try
\* @type: Seq(Int);
INPUT_SEQ == << 1, 5, 6, 10, 23, 24 >>
\* the element to search for
INPUT_KEY == 10

\* introduce the variables to be used in BinSearch
VARIABLES
    \* @type: Int;
    low,
    \* @type: Int;
    high,
    \* @type: Bool;
    isTerminated,
    \* @type: Int;
    returnValue

\* use an instance for the fixed constants
INSTANCE BinSearch

===============================================================================