#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <emscripten.h>
#include <stdint.h>
#include <memory.h>
#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>

#include "miniz.h"
#include "utf8.h"
#include "stem.h"

#include "pjson.h"

#define uprintf printf
#define sprintf_s sprintf
#define _stricmp strcasecmp
#define _strnicmp strncasecmp

typedef std::vector<uint8_t> uint8_vec;

static void *g_pMaj_data;
static pjson::document g_doc;
static std::string g_result_str;

static void strcpy_s(char* pDst, size_t dst_size, const char* pSrc)
{
    assert(pSrc && pDst);
    assert(dst_size);
    if (!pSrc || !pDst || !dst_size)
        return;

    size_t l = strlen(pSrc);
    if (l > (dst_size - 1))
        l = (dst_size - 1);
    
    memcpy(pDst, pSrc, l);
    pDst[l] = '\0';
}

static void panic(const char *pMsg, ...)
{
    char buf[4096];

    va_list args;
    va_start(args, pMsg);
    vsnprintf(buf, sizeof(buf), pMsg, args);
    va_end(args);

    fprintf(stderr, "%s", buf);

    exit(EXIT_FAILURE);
}

static inline int iabs(int v)
{
    if (v < 0)
    {
        assert(v != INT_MIN);
        return -v;
    }

    return v;
}

// like isupper() but doesn't assert on negative values and doesn't factor in locale
static inline bool uisupper(char c)
{
    return (c >= 'A') && (c <= 'Z');
}

static inline bool uisupper(uint8_t c)
{
    return (c >= 'A') && (c <= 'Z');
}

// like islower() but doesn't assert on negative values and doesn't factor in locale
static inline bool uislower(char c)
{
    return (c >= 'a') && (c <= 'z');
}

static inline bool uislower(uint8_t c)
{
    return (c >= 'a') && (c <= 'z');
}

// like isdigit() but doesn't assert on negative values and doesn't factor in locale
static inline bool uisdigit(char c)
{
    return (c >= '0') && (c <= '9');
}

static inline bool uisdigit(uint8_t c)
{
    return (c >= '0') && (c <= '9');
}

static uint32_t hash_hsieh(const uint8_t* pBuf, size_t len)
{
    if (!pBuf || !len)
        return 0;

    uint32_t h = static_cast<uint32_t>(len);

    const uint32_t bytes_left = len & 3;
    len >>= 2;

    while (len--)
    {
        const uint16_t* pWords = reinterpret_cast<const uint16_t*>(pBuf);

        h += pWords[0];

        const uint32_t t = (pWords[1] << 11) ^ h;
        h = (h << 16) ^ t;

        pBuf += sizeof(uint32_t);

        h += h >> 11;
    }

    switch (bytes_left)
    {
    case 1:
        h += *reinterpret_cast<const signed char*>(pBuf);
        h ^= h << 10;
        h += h >> 1;
        break;
    case 2:
        h += *reinterpret_cast<const uint16_t*>(pBuf);
        h ^= h << 11;
        h += h >> 17;
        break;
    case 3:
        h += *reinterpret_cast<const uint16_t*>(pBuf);
        h ^= h << 16;
        h ^= (static_cast<signed char>(pBuf[sizeof(uint16_t)])) << 18;
        h += h >> 11;
        break;
    default:
        break;
    }

    h ^= h << 3;
    h += h >> 5;
    h ^= h << 4;
    h += h >> 17;
    h ^= h << 25;
    h += h >> 6;

    return h;
}

static bool read_binary_file(const char* pFilename, uint8_vec& buf)
{
    FILE* pFile = fopen(pFilename, "rb");
    if (!pFile)
        return false;

    fseek(pFile, 0, SEEK_END);
    int64_t len = ftell(pFile);
    if (len < 0)
    {
        fclose(pFile);
        return false;
    }
    fseek(pFile, 0, SEEK_SET);

    buf.resize(len);

    if (fread(&buf[0], len, 1, pFile) != 1)
    {
        fclose(pFile);
        return false;
    }

    fclose(pFile);
    return true;
}

static bool vformat(std::vector<char>& buf, const char* pFmt, va_list args)
{
    uint32_t buf_size = 8192;

    for (; ; )
    {
        buf.resize(buf_size);

        int res = vsnprintf(&buf[0], buf.size(), pFmt, args);
        if (res == -1)
        {
            assert(false);
            return false;
        }

        if (res <= buf.size() - 1)
            break;

        buf_size *= 2;
        if (buf_size > 16 * 1024 * 1024)
        {
            assert(false);
            return false;
        }
    }
    return true;
}

static std::string string_format(const char* pMsg, ...)
{
    std::vector<char> buf;

    va_list args;
    va_start(args, pMsg);
    if (!vformat(buf, pMsg, args))
        return "";
    va_end(args);

    std::string res;
    if (buf.size())
        res.assign(&buf[0]);

    return res;
}

static std::string string_slice(const std::string& str, size_t ofs, size_t len = UINT32_MAX)
{
    if (!len)
        return "";

    if (ofs > str.size())
    {
        assert(0);
        return "";
    }

    const size_t max_len = str.size() - ofs;

    len = std::min(len, max_len);

    std::string res(str);
    if (ofs)
        res.erase(0, ofs);

    if (len)
        res.resize(len);

    return res;
}

static std::string& string_trim(std::string& str)
{
    while (str.size() && isspace((uint8_t)str.back()))
        str.pop_back();

    while (str.size() && isspace((uint8_t)str[0]))
        str.erase(0, 1);

    return str;
}

static bool string_ends_in(const std::string& str, const char* pPhrase)
{
    const size_t str_len = str.size();

    const size_t phrase_len = strlen(pPhrase);
    assert(phrase_len);

    if (str_len >= phrase_len)
    {
        if (_stricmp(pPhrase, str.c_str() + str_len - phrase_len) == 0)
            return true;
    }

    return false;
}

static bool string_begins_with(const std::string& str, const char* pPhrase)
{
    const size_t str_len = str.size();

    const size_t phrase_len = strlen(pPhrase);
    assert(phrase_len);

    if (str_len >= phrase_len)
    {
        if (_strnicmp(pPhrase, str.c_str(), phrase_len) == 0)
            return true;
    }

    return false;
}

static inline uint8_t utolower(uint8_t c)
{
    if ((c >= 'A') && (c <= 'Z'))
        return (c - 'A') + 'a';
    return c;
}

static int get_next_utf8_code_point_len(const uint8_t* pStr) 
{
    if (pStr == nullptr || *pStr == 0) 
    {
        // Return 0 if the input is null or points to a null terminator
        return 0; 
    }

    const uint8_t firstByte = *pStr;

    if ((firstByte & 0x80) == 0) 
    { 
        // Starts with 0, ASCII character
        return 1;
    }
    else if ((firstByte & 0xE0) == 0xC0) 
    { 
        // Starts with 110
        return 2;
    }
    else if ((firstByte & 0xF0) == 0xE0) 
    { 
        // Starts with 1110
        return 3;
    }
    else if ((firstByte & 0xF8) == 0xF0) 
    { 
        // Starts with 11110
        return 4;
    }
    else 
    {
        // Invalid UTF-8 byte sequence
        return -1;
    }
}

typedef std::vector<std::string> string_vec;
typedef std::vector<unsigned int> uint_vec;

static void get_string_words(
    const std::string& str,
    string_vec& words,
    uint_vec* pOffsets_vec, 
    const char* pAdditional_whitespace = nullptr)
{
    const uint8_t* pStr = (const uint8_t *)str.c_str();

    words.resize(0);
    if (pOffsets_vec)
        pOffsets_vec->resize(0);

    std::string cur_token;
    cur_token.reserve(128);

    std::string whitespace(" \t\n\r,;:.!?()[]*/\"");
    if (pAdditional_whitespace)
        whitespace += std::string(pAdditional_whitespace);
    
    int word_start_ofs = -1;
    
    uint32_t cur_ofs = 0;
    while ((cur_ofs < str.size()) && (pStr[cur_ofs]))
    {
        int l = get_next_utf8_code_point_len(pStr + cur_ofs);
        const uint8_t c = pStr[cur_ofs];

        if (l <= 0)
        {
            assert(0);
            l = 1;
        }

        bool is_whitespace = (whitespace.find_first_of(c) != std::string::npos);

        if ((l == 2) && (c == 0xc2))
        {
            // NO-BREAK SPACE
            if (pStr[cur_ofs + 1] == 0xa0)
                is_whitespace = true;
        }

        if ((l == 2) && (c == 0xCA))
        {
            // single left quote
            if (pStr[cur_ofs + 1] == 0xBB)
                is_whitespace = true;
        }

        if ((l == 3) && (c == 0xE2) && (pStr[cur_ofs + 1] == 0x80))
        {
            // dash
            if (pStr[cur_ofs + 2] == 0x93)
                is_whitespace = true;
            // dash
            if (pStr[cur_ofs + 2] == 0x94)
                is_whitespace = true;
            // left quote
            else if (pStr[cur_ofs + 2] == 0x9C)
                is_whitespace = true;
            // right quote
            else if (pStr[cur_ofs + 2] == 0x9D)
                is_whitespace = true;
            // ellipsis (three dots)
            else if (pStr[cur_ofs + 2] == 0xA)
                is_whitespace = true;
            // ellipsis (three dots)
            else if (pStr[cur_ofs + 2] == 0xA6)
                is_whitespace = true;
            // long dash
            else if (pStr[cur_ofs + 2] == 9)
                is_whitespace = true;
            // left single quote
            else if (pStr[cur_ofs + 2] == 0x98)
                is_whitespace = true;
            // right single quote
            else if (pStr[cur_ofs + 2] == 0x99)
                is_whitespace = true;
            // right double quote
            else if (pStr[cur_ofs + 2] == 0x9D)
                is_whitespace = true;
        }
        
        if (is_whitespace)
        {
            if (cur_token.size())
            {
                words.push_back(cur_token);
                if (pOffsets_vec)
                    pOffsets_vec->push_back(word_start_ofs);

                cur_token.clear();
                word_start_ofs = -1;
            }
        }
        else
        {
            if (word_start_ofs < 0)
                word_start_ofs = cur_ofs;

            for (int i = 0; i < l; i++)
                cur_token.push_back(pStr[cur_ofs + i]);
        }
                
        cur_ofs += l;
    }

    if (cur_token.size())
    {
        words.push_back(cur_token);

        if (pOffsets_vec)
            pOffsets_vec->push_back(word_start_ofs);
    }
}

enum date_prefix_t
{
    cNoPrefix = -1,

    cEarlySpring,
    cEarlySummer,
    cEarlyAutumn,
    cEarlyFall,
    cEarlyWinter,

    cMidSpring,
    cMidSummer,
    cMidAutumn,
    cMidFall,
    cMidWinter,

    cLateSpring,
    cLateSummer,
    cLateAutumn,
    cLateFall,
    cLateWinter,

    cSpring,
    cSummer,
    cAutumn,
    cFall,
    cWinter,

    cEarly,
    cMiddleOf,
    cLate,
    cEndOf,

    cTotalPrefixes
};

const uint32_t NUM_DATE_PREFIX_STRINGS = 24;
const char* g_date_prefix_strings[NUM_DATE_PREFIX_STRINGS] =
{
    "Early Spring",
    "Early Summer",
    "Early Autumn",
    "Early Fall",
    "Early Winter",

    "Mid Spring",
    "Mid Summer",
    "Mid Autumn",
    "Mid Fall",
    "Mid Winter",

    "Late Spring",
    "Late Summer",
    "Late Autumn",
    "Late Fall",
    "Late Winter",

    "Spring",
    "Summer",
    "Autumn",
    "Fall",
    "Winter",

    "Early",
    "Mid",
    "Late",
    "End of"
};

struct event_date
{
    date_prefix_t m_prefix;

    int m_year;
    int m_month;    // 1 based: [1,12] (NOT ZERO BASED), -1=invalid
    int m_day;      // 1 based: [1,31], -1=invalid

    bool m_fuzzy; // ?
    bool m_plural; // 's

    bool m_approx; // (approximate)
    bool m_estimated; // (estimated)

    event_date();

    event_date(const event_date& other);

    bool sanity_check() const;

    bool operator== (const event_date& rhs) const;

    bool operator!= (const event_date& rhs) const;

    event_date& operator =(const event_date& rhs);

    void clear();

    bool is_valid() const;

    std::string get_string() const;

    // Parses basic dates (not ranges). 
    // Date can end in "(approximate)", "(estimated)", "?", or "'s".
    // 2 digit dates converted to 1900+.
    // Supports year, month/year, or month/day/year.
    bool parse(const char* pStr, bool fix_20century_dates);

    void get_sort_date(int& year, int& month, int& day) const;
    static bool compare(const event_date& lhs, const event_date& rhs);
};

// Note the returned date may be invalid. It's only intended for sorting/comparison purposes against other sort dates.
void event_date::get_sort_date(int& year, int& month, int& day) const
{
    year = m_year;
    month = 0;
    day = 0;

    if (m_month == -1)
    {
        // All we have is a year, no month or date supplied.
        if (m_plural)
        {
            const bool is_century = (m_year % 100) == 0;
            const bool is_decade = (m_year % 10) == 0;

            // 1900's, 1910's, 1800's etc.
            if (m_prefix == cEarly)
            {
#if 0
                if (is_century)
                    year += 10;
                else if (is_decade)
                    year += 1;
#endif
                day = -1;
            }
            else if (m_prefix == cMiddleOf)
            {
                if (is_century)
                    year += 50;
                else if (is_decade)
                    year += 5;
            }
            else if (m_prefix == cLate)
            {
                if (is_century)
                    year += 80;
                else if (is_decade)
                    year += 8;
            }
            else if (m_prefix == cEndOf)
            {
                if (is_century)
                    year += 90;
                else if (is_decade)
                    year += 9;
            }
            else
            {
                // 1980's goes before 1980
                day = -1;
            }
        }
        else
        {
            // 1900, 1910, 1800 etc.
            switch (m_prefix)
            {
            case cEarlySpring:
            {
                month = 3;
                day = 1;
                break;
            }
            case cEarlySummer:
            {
                month = 6;
                day = 1;
                break;
            }
            case cEarlyAutumn:
            {
                month = 9;
                day = 1;
                break;
            }
            case cEarlyFall:
            {
                month = 9;
                day = 1;
                break;
            }
            case cEarlyWinter:
            {
                month = 12;
                day = 1;
                break;
            }
            case cMidSpring:
            {
                month = 4;
                day = 1;
                break;
            }
            case cMidSummer:
            {
                month = 7;
                day = 1;
                break;
            }
            case cMidAutumn:
            {
                month = 10;
                day = 1;
                break;
            }
            case cMidFall:
            {
                month = 10;
                day = 1;
                break;
            }
            case cMidWinter:
            {
                month = 1;
                day = 1;
                break;
            }
            case cLateSpring:
            {
                month = 5;
                day = 15;
                break;
            }
            case cLateSummer:
            {
                month = 8;
                day = 15;
                break;
            }
            case cLateAutumn:
            {
                month = 11;
                day = 15;
                break;
            }
            case cLateFall:
            {
                month = 11;
                day = 15;
                break;
            }
            case cLateWinter:
            {
                month = 2;
                day = 15;
                break;
            }
            case cEarly:
            {
                day = 1;
                break;
            }
            case cSpring:
            {
                month = 3;
                day = 20;
                break;
            }
            case cSummer:
            {
                month = 6;
                day = 21;
                break;
            }
            case cMiddleOf:
            {
                month = 6;
                day = 15;
                break;
            }
            case cAutumn:
            {
                month = 9;
                day = 23;
                break;
            }
            case cFall:
            {
                month = 9;
                day = 23;
                break;
            }
            case cLate:
            {
                month = 10;
                day = 15;
                break;
            }
            case cWinter:
            {
                month = 12;
                day = 21;
                break;
            }
            case cEndOf:
            {
                month = 12;
                day = 1;
                break;
            }
            default:
                break;
            }
        }
    }
    else if (m_day == -1)
    {
        // We have a year and a month, but no date
        month = m_month;

        // 1/1900, 4/1910, 12/1805 etc.
        switch (m_prefix)
        {
        case cEarly:
        {
            day = 2;
            break;
        }
        case cMiddleOf:
        {
            day = 15;
            break;
        }
        case cLate:
        {
            day = 25;
            break;
        }
        case cEndOf:
        {
            day = 28;
            break;
        }
        default:
            break;
        }
    }
    else
    {
        month = m_month;
        day = m_day;
    }
}

// Compares two timeline dates. true if lhs < rhs
bool event_date::compare(const event_date& lhs, const event_date& rhs)
{
    int lhs_year, lhs_month, lhs_day;
    lhs.get_sort_date(lhs_year, lhs_month, lhs_day);

    int rhs_year, rhs_month, rhs_day;
    rhs.get_sort_date(rhs_year, rhs_month, rhs_day);

    if (lhs_year < rhs_year)
        return true;
    else if (lhs_year == rhs_year)
    {
        if (lhs_month < rhs_month)
            return true;
        else if (lhs_month == rhs_month)
        {
            if (lhs_day < rhs_day)
                return true;
        }
    }

    return false;
}

static bool is_season(date_prefix_t prefix)
{
    switch (prefix)
    {
    case cEarlySpring:
    case cEarlySummer:
    case cEarlyAutumn:
    case cEarlyFall:
    case cEarlyWinter:

    case cMidSpring:
    case cMidSummer:
    case cMidAutumn:
    case cMidFall:
    case cMidWinter:

    case cLateSpring:
    case cLateSummer:
    case cLateAutumn:
    case cLateFall:
    case cLateWinter:

    case cSpring:
    case cSummer:
    case cAutumn:
    case cFall:
    case cWinter:
        return true;
    default:
        break;
    }

    return false;
}

event_date::event_date()
{
    clear();
}

event_date::event_date(const event_date& other)
{
    *this = other;
}

bool event_date::sanity_check() const
{
    if (m_year == -1)
        return false;

    if ((m_month == 0) || (m_day == 0))
        return false;

    if ((m_month < -1) || (m_month > 12))
        return false;

    if ((m_day < -1) || (m_day > 31))
        return false;

    if (m_plural)
    {
        if (m_month != -1)
            return false;
    }

    if (m_month == -1)
    {
        if (m_day != -1)
            return false;
    }

    if (is_season(m_prefix))
    {
        if (m_month != -1)
            return false;

        if (m_day != -1)
            return false;
    }
    else if ((m_prefix >= cEarly) && (m_prefix <= cEndOf))
    {
        if (m_day != -1)
            return false;
    }

    return true;
}

bool event_date::operator== (const event_date& rhs) const
{
    return (m_prefix == rhs.m_prefix) &&
        (m_year == rhs.m_year) &&
        (m_month == rhs.m_month) &&
        (m_day == rhs.m_day) &&
        (m_fuzzy == rhs.m_fuzzy) &&
        (m_plural == rhs.m_plural) &&
        (m_approx == rhs.m_approx) &&
        (m_estimated == rhs.m_estimated);
}

bool event_date::operator!= (const event_date& rhs) const
{
    return !(*this == rhs);
}

event_date& event_date::operator =(const event_date& rhs)
{
    m_prefix = rhs.m_prefix;
    m_year = rhs.m_year;
    m_month = rhs.m_month;
    m_day = rhs.m_day;
    m_fuzzy = rhs.m_fuzzy;
    m_plural = rhs.m_plural;
    m_approx = rhs.m_approx;
    m_estimated = rhs.m_estimated;
    return *this;
}

void event_date::clear()
{
    m_prefix = cNoPrefix;

    m_year = -1;
    m_month = -1;
    m_day = -1;

    m_fuzzy = false; //?
    m_plural = false; // 's
    m_approx = false; // (approximate)
    m_estimated = false; // (estimated)
}

bool event_date::is_valid() const
{
    return m_year != -1;
}

std::string event_date::get_string() const
{
    if (m_year == -1)
        return "";

    std::string res;

    if (m_prefix != cNoPrefix)
    {
        res = g_date_prefix_strings[m_prefix];
        res += " ";
    }

    if (m_month == -1)
    {
        assert(m_day == -1);

        char buf[256];
        sprintf_s(buf, "%i", m_year);
        res += buf;
    }
    else if (m_day == -1)
    {
        assert(m_month >= 1 && m_month <= 12);

        char buf[256];
        sprintf_s(buf, "%u/%i", m_month, m_year);
        res += buf;
    }
    else
    {
        assert(m_month >= 1 && m_month <= 12);

        char buf[256];
        sprintf_s(buf, "%u/%u/%i", m_month, m_day, m_year);
        res += buf;
    }

    if (m_plural)
        res += "'s";

    if (m_fuzzy)
        res += "?";

    if (m_approx)
        res += " (approximate)";

    if (m_estimated)
        res += " (estimated)";

    return res;
}

// Parses basic dates (not ranges). Works with dates returned by get_string().
// Date can end in "(approximate)", "(estimated)", "?", or "'s".
// 2 digit dates converted to 1900+.
// Supports year, month/year, or month/day/year.
bool event_date::parse(const char* pStr, bool fix_20century_dates)
{
    clear();

    std::string temp(pStr);

    string_trim(temp);

    if (!temp.size())
        return false;

    if (isalpha(temp[0]))
    {
        uint32_t i;
        for (i = 0; i < cTotalPrefixes; i++)
            if (string_begins_with(temp, g_date_prefix_strings[i]))
                break;
        if (i == cTotalPrefixes)
            return false;

        temp.erase(0, strlen(g_date_prefix_strings[i]));

        m_prefix = static_cast<date_prefix_t>(i);
    }

    string_trim(temp);

    if (!temp.size())
        return false;

    if (string_ends_in(temp, "(approximate)"))
    {
        m_approx = true;
        temp.resize(temp.size() - strlen("(approximate)"));
    }
    else if (string_ends_in(temp, "(estimated)"))
    {
        m_estimated = true;
        temp.resize(temp.size() - strlen("(estimated)"));
    }

    string_trim(temp);

    if (!temp.size())
        return false;

    if (string_ends_in(temp, "?"))
    {
        m_fuzzy = true;
        temp.resize(temp.size() - 1);

        string_trim(temp);
    }

    if (string_ends_in(temp, "'s"))
    {
        m_plural = true;
        temp.resize(temp.size() - 2);

        string_trim(temp);
    }

    if (!temp.size())
        return false;

    int num_slashes = 0;
    std::string date_strs[3];

    for (size_t i = 0; i < temp.size(); i++)
    {
        if (temp[i] == '/')
        {
            num_slashes++;
            if (num_slashes == 3)
                return false;
        }
        else if (isdigit(temp[i]))
        {
            date_strs[num_slashes] += temp[i];
        }
        else
        {
            return false;
        }
    }

    if (num_slashes == 0)
    {
        m_year = atoi(date_strs[0].c_str());
    }
    else if (num_slashes == 1)
    {
        m_month = atoi(date_strs[0].c_str());
        if ((m_month < 1) || (m_month > 12))
            return false;

        m_year = atoi(date_strs[1].c_str());
    }
    else
    {
        m_month = atoi(date_strs[0].c_str());
        if ((m_month < 1) || (m_month > 12))
            return false;

        m_day = atoi(date_strs[1].c_str());
        if ((m_day < 1) || (m_day > 31))
            return false;

        m_year = atoi(date_strs[2].c_str());
    }

    if (fix_20century_dates)
    {
        if ((m_year >= 1) && (m_year <= 99))
            m_year += 1900;
    }

    if ((m_year < 0) || (m_year > 2100))
        return false;

    return true;
}

static void init_norm();

static std::vector<event_date> g_event_dates, g_event_end_dates;

typedef std::vector<uint32_t> uint32_vec;

struct custom_string_hash
{
    inline std::size_t operator()(const std::string& s) const 
    {
        if (!s.size())
            return 0;
        return hash_hsieh((const uint8_t *)s.c_str(), s.size() + 1);
    }
};

typedef std::unordered_map<std::string, uint32_vec, custom_string_hash> word_index_t;

static word_index_t g_word_index;
static std::unordered_set<std::string> g_unique_sources;

static void init_inverted_index()
{
    printf("Building inverted index\n");

    const auto& root_arr = g_doc[0];
    assert(root_arr.is_array());

    g_word_index.reserve(root_arr.size());

    string_vec search_words;
    search_words.reserve(256);

    std::string source_str;
    source_str.reserve(64);

    g_unique_sources.reserve(16);
    g_unique_sources.clear();

    for (uint32_t json_arr_index = 0; json_arr_index < root_arr.size(); json_arr_index++)
    {
        const auto& obj = root_arr[json_arr_index];

        const char* pSource = obj.find_string_ptr("source");
        if ((!pSource) || (!pSource[0]))
            continue;

        source_str = pSource;
        g_unique_sources.insert(source_str);

        const char* pSearch = obj.find_string_ptr("search");
        if (!pSearch)
            continue;

        get_string_words(pSearch, search_words, nullptr, "-");

        for (uint32_t i = 0; i < search_words.size(); i++)
        {
            auto f = g_word_index.insert(std::make_pair(search_words[i], uint32_vec()));

            (f.first)->second.push_back(json_arr_index);
        }
    }

    for (auto& r : g_word_index)
    {
        std::sort(r.second.begin(), r.second.end());
        auto last = std::unique(r.second.begin(), r.second.end());
        r.second.resize(last - r.second.begin());
    }

    printf("Total unique words: %zu, unique sources: %zu\n", g_word_index.size(), g_unique_sources.size());
}

static void init_dates()
{
    printf("Parsing dates\n");

    const auto& root_arr = g_doc[0];
    assert(root_arr.is_array());

    g_event_dates.resize(root_arr.size());
    g_event_end_dates.resize(root_arr.size());

    for (uint32_t json_arr_index = 0; json_arr_index < root_arr.size(); json_arr_index++)
    {
        const auto& obj = root_arr[json_arr_index];

        const char* pDate = obj.find_string_ptr("date");
        if (!pDate)
            continue;

        if (!g_event_dates[json_arr_index].parse(pDate, false))
            printf("Failed parsing event date %u!\n", json_arr_index);

        const char* pEnd_date = obj.find_string_ptr("end_date");
        if ((pEnd_date) && (pEnd_date[0]))
        {
            if (!g_event_end_dates[json_arr_index].parse(pEnd_date, false))
                printf("Failed parsing event end date %u!\n", json_arr_index);
        }
    }
}

EMSCRIPTEN_KEEPALIVE
extern "C" int get_num_sources()
{
    return (int)g_unique_sources.size();
}

EMSCRIPTEN_KEEPALIVE
extern "C" const char* get_source(int id)
{
    int cur_index = 0;

    for (const auto& src : g_unique_sources)
    {
        if (cur_index == id)
            return src.c_str();
        cur_index++;
    }

    return "";
}

EMSCRIPTEN_KEEPALIVE
extern "C" void init()
{
    printf("init() start\n");

    init_norm();
            
    printf("Opening archive\n");
    
    mz_zip_archive zip_archive;
    memset(&zip_archive, 0, sizeof(zip_archive));
    mz_bool status = mz_zip_reader_init_file(&zip_archive, "majestic.zip", 0);
    if (!status)
        panic("Failed reading majestic.zip");
    
    printf("Extracting from archive\n");
    
    size_t uncomp_size = 0;
    g_pMaj_data = mz_zip_reader_extract_file_to_heap(&zip_archive, "majestic.json", &uncomp_size, 0);
    if (!g_pMaj_data)
        panic("Failed extracting majestic.json");
        
    mz_zip_reader_end(&zip_archive);
    
    g_pMaj_data = realloc(g_pMaj_data, uncomp_size + 1);
    if (!g_pMaj_data)
        panic("Out of memory");
    
    ((uint8_t *)g_pMaj_data)[uncomp_size] = 0;
    uncomp_size++;
    
    printf("Deserializing JSON data\n");
              
    uint8_t *pJSON = &((uint8_t *)g_pMaj_data)[0];
    uint32_t json_len = (uint32_t)uncomp_size;
            
    // Skip BOM
    if ((json_len >= 4) && (pJSON[0] == 0xef))
    {
        json_len -= 3;
        pJSON += 3;
    }
            
    status = g_doc.deserialize_in_place((char *)pJSON);
    if (!status)
        panic("JSON deserialize failed");
    
    if (!g_doc.is_object() || (g_doc.size() != 1))
        panic("Invalid JSON");

    g_result_str.reserve(64 * 1024);
    
    init_inverted_index();

    init_dates();
    
    printf("init() OK\n");
}

struct char_map
{
    const char32_t* m_pFrom;
    const char m_to;
};

static const char_map g_char_norm_up[] =
{
    { U"ÁĂẮẶẰẲẴǍÂẤẬẦẨẪÄǞȦǠẠȀÀẢȂĀĄÅǺḀÃǼǢȺΆ", 'A' },
    { U"ḂḄḆƁƂƄ", 'B' },
    { U"ĆČÇḈĈĊƇȻƆ", 'C' },
    { U"ĎḐḒḊḌḎĐƉƊƋǱǲǄ", 'D' },
    { U"ÉĔĚȨḜÊẾỆỀỂỄḘËĖẸȄÈẺȆĒḖḔĘẼḚÈÊËĒĔĖĘĚƐƎƏȄȆȨΈΉΕƐƐ", 'E' },
    { U"ḞƑ", 'F' },
    { U"ǴĞǦĢĜĠḠĜĞĠĢƓǤǦǴƔ", 'G' },
    { U"ḪȞḨĤḦḢḤĤĦǶȞΗǶ", 'H' },
    { U"ÍĬǏÎÏḮİỊȈÌỈȊĪĮĨḬÌÍÎÏĨĪĬĮİƗǏȈȊ", 'I' },
    { U"ĴĴ", 'J' },
    { U"ḰǨĶḲḴĶƘǨΚ", 'K' },
    { U"ĹĽĻḼḶḸḺĹĻĽĿŁΛ", 'L' },
    { U"ḾṀṂƜ", 'M' },
    { U"ŃŇŅṊṄṆǸṈÑÑŃŅŇŊƝǸΝ", 'N' },
    { U"ÓŎǑÔỐỘỒỔỖÖȪȮȰỌŐȌÒỎƠỚỢỜỞỠȎŌṒṐǪǬÕṌṎȬǾØÒÓÔÕÖØŌŎŐƟƠǑǪǬǾȌȎȪȬȮȰΌΟΩ", 'O' },
    { U"ṔṖΠΡΦ", 'P' },
    { U"ŔŘŖṘṚṜȐȒṞŔŖŘƦȐȒ", 'R' },
    { U"ŚṤŠṦŞŜȘṠṢṨßŚŜŞŠƩȘΣ", 'S' },
    { U"ŤŢṰȚṪṬṮŢŤŦƬƮȚΤ", 'T' },
    { U"ÚŬǓÛṶÜǗǙǛǕṲỤŰȔÙỦƯỨỰỪỬỮȖŪṺŲŮŨṸṴÙÚÛÜŨŪŬŮŰŲƯǓǕǗǙǛȔȖ", 'U' },
    { U"ṾṼƲ", 'V' },
    { U"ẂŴẄẆẈẀŴ", 'W' },
    { U"ẌẊΧΞ", 'X' },
    { U"ÝŶŸẎỴỲỶȲỸÝŶŸƳȲΥΎΫ", 'Y' },
    { U"ŹŽẐŻẒẔŹŻŽƵƷǮȤΖ", 'Z' },
};

static const char_map g_char_norm_lower[] =
{
    { U"áăắặằẳẵǎâấậầẩẫäǟȧǡạȁàảȃāąåǻḁãǽǣⱥάàáâãäåāăąǎǟǡǻȁȃȧάα", 'a' },
    { U"ḃḅḇɓƃƅƀƃβƀƃƅ", 'b' },
    { U"ćčçḉĉċƈȼɔƈçćĉċčƈȼ", 'c' },
    { U"ďḑḓḋḍḏđɖɗƌǳǳǆƌďđƌǳǆȡďđƌǳǆȡ", 'd' },
    { U"éĕěȩḝêếệềểễḙëėẹȅèẻȇēḗḕęẽḛèêëēĕėęěɛǝəȅȇȩέήεɛɛèéêëēĕėęěȅȇȩε", 'e' },
    { U"ḟƒ", 'f' },
    { U"ǵğǧģĝġḡĝğġģɠǥǧǵɣĝğġģǧǵ", 'g' },
    { U"ḫȟḩĥḧḣḥẖĥħƕƕȟƕĥħȟ", 'h' },
    { U"íĭǐîïḯiịȉìỉȋīįĩḭìíîïĩīĭįiɨǐȉȋìíîïĩīĭįǐȉȋι", 'i' },
    { U"ǰĵĵǰĵǰ", 'j' },
    { U"ḱǩķḳḵķƙǩκƙķƙǩκ", 'k' },
    { U"ĺľļḽḷḹḻĺļľŀłƚƛλƚĺļľŀłƚλƚ", 'l' },
    { U"ḿṁṃɯ", 'm' },
    { U"ńňņṋṅṇǹṉññńņňŋɲǹνƞñńņňŉŋƞǹη", 'n' },
    { U"óŏǒôốộồổỗöȫȯȱọőȍòỏơớợờởỡȏōṓṑǫǭõṍṏȭǿøòóôõöøōŏőɵơǒǫǭǿȍȏȫȭȯȱόοòóôõöøōŏőơǒǫǭǿȍȏȫȭȯȱοσ", 'o' },
    { U"ṕṗπφƥ", 'p' },
    { U"ŕřŗṙṛṝȑȓṟŕŗřʀȑȓρŕŗřȑȓρ", 'r' },
    { U"śṥšṧşŝșṡẛṣṩśŝşšʃșƨśŝşšșƨȿ", 's' },
    { U"ťţṱțẗṫṭṯţťŧƭʈțτƫţťŧƭțτ", 't' },
    { U"úŭǔûṷüǘǚǜǖṳụűȕùủưứựừửữȗūṻųůũṹṵùúûüũūŭůűųưǔǖǘǚǜȕȗưùúûüũūŭůűųưǔǖǘǚǜȕȗμ", 'u' },
    { U"ṿṽʋ", 'v' },
    { U"ẃŵẅẇẉẁẘŵŵω", 'w' },
    { U"ẍẋχξχξ", 'x' },
    { U"ýŷÿẏỵỳỷȳẙỹýŷÿƴȳυύϋƴýÿŷƴȳγψ", 'y' },
    { U"źžẑżẓẕźżžƶʒǯȥζƶźżžƶƹȥζ", 'z' },
};

static std::map<int, int> g_upper_trans;
static std::map<int, int> g_lower_trans;

static const char* g_stop_words[] =
{
    "a", "about", "above", "after", "again", "against", "all", "am", "an", "and", "any", "are", "as",
    "at", "be", "because", "been", "before", "being", "below", "between", "both", "but", "by", "can",
    "could", "did", "do", "does", "doing", "down", "during", "each", "few", "for", "from",
    "further", "had", "has", "have", "having", "he", "her", "here", "hers", "herself", "him", "himself",
    "his", "how", "i", "if", "in", "into", "is", "it", "its", "itself", "just", "me", "more", "most",
    "my", "myself", "no", "nor", "not", "now", "of", "off", "on", "once", "only", "or", "other", "our",
    "ours", "ourselves", "out", "over", "own", "re", "same", "she", "should", "so", "some", "such",
    "than", "that", "the", "their", "theirs", "them", "themselves", "then", "there", "these", "they",
    "this", "those", "through", "to", "too", "under", "until", "up", "very", "was", "we", "were", "what",
    "when", "where", "which", "while", "who", "whom", "why", "will", "with", "you", "your", "yours",
    "yourself", "yourselves", "although", "also", "already", "another", "seemed", "seem", "seems"
};
static const uint32_t NUM_STOP_WORDS = (uint32_t)std::size(g_stop_words);

std::set<std::string> g_stop_words_set;

static void init_norm()
{
    g_stop_words_set.clear();
    for (const auto& str : g_stop_words)
        g_stop_words_set.insert(str);

    for (uint32_t i = 0; i < std::size(g_char_norm_up); i++)
    {
        const char32_t* pFrom = g_char_norm_up[i].m_pFrom;
        char to_char = g_char_norm_up[i].m_to;

        while (*pFrom)
        {
            char32_t fc = *pFrom++;

            auto f = g_upper_trans.find(fc);
            if (f != g_upper_trans.end())
            {
                if (f->second != to_char)
                {
                    uprintf("Upper char %u 0x%x is redundant\n", fc, fc);
                    exit(1);
                }
            }

            g_upper_trans[fc] = to_char;
        }
    }

    for (uint32_t i = 0; i < std::size(g_char_norm_lower); i++)
    {
        const char32_t* pFrom = g_char_norm_lower[i].m_pFrom;
        char to_char = g_char_norm_lower[i].m_to;

        while (*pFrom)
        {
            char32_t fc = *pFrom++;

            auto f = g_upper_trans.find(fc);
            if (f != g_upper_trans.end())
            {
                uprintf("Lower char %u 0x%x is in the upper table\n", fc, fc);

                if (utolower((uint8_t)f->second) != to_char)
                    uprintf("Conversion mismatch %u 0x%x\n", fc, fc);

                //exit(1);
            }

            f = g_lower_trans.find(fc);
            if (f != g_lower_trans.end())
            {
                if (f->second != to_char)
                {
                    uprintf("Lower char %u 0x%x is redundant\n", fc, fc);
                    exit(1);
                }
            }

            g_lower_trans[fc] = to_char;
        }
    }
}

// Resulting characters are guaranteed to be <128 - useful for searching purposes. 
// Unrecognized Unicode characters are deleted.
static void normalize_diacritics(const char* pStr, std::string& res)
{
    assert(g_stop_words_set.size());

    res.resize(0);

    while (*pStr)
    {
        int l = get_next_utf8_code_point_len((const uint8_t*)pStr);
        const uint8_t c = *pStr;

        utf8_int32_t cp;
        char* pStr_next = utf8codepoint(pStr, &cp);

        assert((pStr_next - pStr) == l);

        if (cp < 128)
        {
            res.push_back((char)cp);
            pStr = pStr_next;
            continue;
        }

        int new_char = -1;

        auto u_it = g_upper_trans.find(cp);
        auto l_it = g_lower_trans.find(cp);

        if (u_it != g_upper_trans.end())
            new_char = u_it->second;
        else if (l_it != g_lower_trans.end())
            new_char = l_it->second;
        else
        {
            // FIXME: this is lame, it parses the utf8 directly.

            if ((l == 2) && (c == 0xc2))
            {
                // NO-BREAK SPACE
                if ((uint8_t)pStr[1] == 0xa0)
                    new_char = ' ';
            }

            if ((l == 2) && (c == 0xCA))
            {
                // single left quote
                if ((uint8_t)pStr[1] == 0xBB)
                    new_char = '\'';
            }

            if ((l == 3) && (c == 0xE2) && ((uint8_t)pStr[1] == 0x80))
            {
                // dash
                if ((uint8_t)pStr[2] == 0x93)
                    new_char = '-';
                // dash
                else if ((uint8_t)pStr[2] == 0x94)
                    new_char = '-';
                // left quote
                else if ((uint8_t)pStr[2] == 0x9C)
                    new_char = '"';
                // right quote
                else if ((uint8_t)pStr[2] == 0x9D)
                    new_char = '"';
                // ellipsis (three dots)
                else if ((uint8_t)pStr[2] == 0xA)
                    new_char = '.';
                // ellipsis (three dots)
                else if ((uint8_t)pStr[2] == 0xA6)
                    new_char = '.';
                // long dash
                else if ((uint8_t)pStr[2] == 9)
                    new_char = '-';
                // left single quote
                else if ((uint8_t)pStr[2] == 0x98)
                    new_char = '\'';
                // right single quote
                else if ((uint8_t)pStr[2] == 0x99)
                    new_char = '\'';
                // right double quote
                else if ((uint8_t)pStr[2] == 0x9D)
                    new_char = '"';
            }
        }

        // TODO: Do something smarter?
        if (new_char != -1)
            res.push_back((char)new_char);

        pStr = pStr_next;
    }
}

static std::string normalize_word(const std::string& str)
{
    assert(g_stop_words_set.size());

    const uint32_t MAX_STRING_SIZE = 4096;

    if (str.size() > MAX_STRING_SIZE)
        panic("String too long");

    char buf[MAX_STRING_SIZE + 1];
    strcpy_s(buf, sizeof(buf), str.c_str());

    // Convert utf8 string to lower
    utf8lwr(buf);

    // Remove diacritics and some specials from utf8, this preserves all 1-127 chars
    std::string norm;
    norm.reserve(strlen(buf));

    normalize_diacritics(buf, norm);

    // Remove any non-letter or non-digit characters (we assume this is a word, so whitespace gets removed too)
    std::string temp;
    temp.reserve(norm.size());

    for (uint32_t i = 0; i < norm.size(); i++)
    {
        uint8_t c = norm[i];

        c = utolower(c);

        if (uislower(c) || uisdigit(c))
            temp.push_back(c);
    }

    // Stem word
    strcpy_s(buf, sizeof(buf), temp.c_str());
    if (buf[0])
    {
        int32_t new_len = stem(buf, 0, (int)strlen(buf) - 1);
        buf[new_len + 1] = '\0';
    }

    return buf;
}

// Assumes word is plain ASCII lowercase
static bool is_stop_word(const std::string& word)
{
    assert(g_stop_words_set.size());

    return g_stop_words_set.count(word) != 0;
}

static std::string ustrlwr(const std::string& s)
{
    const size_t l = s.size();

    std::vector<uint8_t> temp;
    temp.resize(l + 1);

    memcpy(&temp[0], s.c_str(), l);
    temp[l] = '\0';

    utf8lwr((char*)&temp[0]);

    return (char*)&temp[0];
}

static int g_num_results;

enum search_t
{
    cInOrder = 0,
    cAny = 1,
    cAll = 2,
    cPreciseCaseSens = 3,
    cPreciseCaseInsens = 4
};

static bool check_for_match(const char* pDesc, const char* pStr, search_t st, const string_vec& str_words)
{
    if (st == cPreciseCaseSens)
        return utf8str(pDesc, pStr) != nullptr;
    else if (st == cPreciseCaseInsens)
        return utf8casestr(pDesc, pStr) != nullptr;
    else
    {
        const bool case_sensitive = true;

        if (!str_words.size())
            return false;
                
        string_vec desc_words;
        desc_words.reserve(256);
        get_string_words(pDesc, desc_words, nullptr, "-");

        if (st == cAny)
        {
            for (uint32_t i = 0; i < desc_words.size(); i++)
            {
                for (uint32_t j = 0; j < str_words.size(); j++)
                {
                    bool matches;
                    if (case_sensitive)
                        matches = (utf8cmp(desc_words[i].c_str(), str_words[j].c_str()) == 0);
                    else
                        matches = (utf8casecmp(desc_words[i].c_str(), str_words[j].c_str()) == 0);

                    if (matches)
                        return true;
                }
            }
        }
        else if (st == cAll)
        {
            std::vector<bool> found_str_word(str_words.size());

            for (uint32_t i = 0; i < desc_words.size(); i++)
            {
                for (uint32_t j = 0; j < str_words.size(); j++)
                {
                    bool matches;
                    if (case_sensitive)
                        matches = (utf8cmp(desc_words[i].c_str(), str_words[j].c_str()) == 0);
                    else
                        matches = (utf8casecmp(desc_words[i].c_str(), str_words[j].c_str()) == 0);

                    if (matches)
                        found_str_word[j] = true;
                }
            }

            for (uint32_t i = 0; i < found_str_word.size(); i++)
                if (!found_str_word[i])
                    return false;

            return true;
        }
        else if (st == cInOrder)
        {
            if (str_words.size() > desc_words.size())
                return false;

            for (int i = 0; i <= (int)desc_words.size() - (int)str_words.size(); i++)
            {
                uint32_t j;
                for (j = 0; j < str_words.size(); j++)
                {
                    bool matches;
                    if (case_sensitive)
                        matches = (utf8cmp(desc_words[i + j].c_str(), str_words[j].c_str()) == 0);
                    else
                        matches = (utf8casecmp(desc_words[i + j].c_str(), str_words[j].c_str()) == 0);

                    if (!matches)
                        break;
                }

                if (j == str_words.size())
                    return true;
            }
        }
        else
        {
            panic("Invalid search type");
        }
    }

    return false;
}

static void print(std::string& str, const pjson::value_variant& obj, const char* pFmt)
{
    str += string_format(pFmt, obj.as_string().c_str());
}

static bool print_value_variant(std::string& str, const pjson::value_variant& obj, const char* pKey, const char* pFmt)
{
    const pjson::value_variant* pVariant = obj.find_value_variant(pKey);
    if (!pVariant)
        return false;

    if (pVariant->is_array())
    {
        for (uint32_t i = 0; i < pVariant->size(); i++)
            print(str, (*pVariant)[i], pFmt);
    }
    else
        print(str, (*pVariant), pFmt);

    return true;
}

static void get_date_range(const event_date& evt, event_date& begin, event_date& end)
{
    assert(evt.is_valid());

    begin.clear();
    end.clear();

    begin.m_year = evt.m_year;
    end.m_year = evt.m_year;

    const bool has_prefix = (evt.m_prefix != cNoPrefix);

    if ((evt.m_month == -1) && (evt.m_day == -1))
    {
        // Year only

        if (has_prefix)
        {
            switch (evt.m_prefix)
            {
            case cEarlySpring:
                begin.m_month = 3;
                begin.m_day = 20;
                end.m_month = 4;
                end.m_day = 10;
                break;
            case cEarlySummer:
                begin.m_month = 6;
                begin.m_day = 21;
                end.m_month = 7;
                end.m_day = 10;
                break;
            case cEarlyAutumn:
            case cEarlyFall:
                begin.m_month = 9;
                begin.m_day = 23;
                end.m_month = 10;
                end.m_day = 10;
                break;
            case cEarlyWinter:
                begin.m_month = 12;
                begin.m_day = 21;
                end.m_month = 1;
                end.m_day = 10;
                break;
            case cMidSpring:
                begin.m_month = 4;
                begin.m_day = 11;
                end.m_month = 5;
                end.m_day = 10;
                break;
            case cMidSummer:
                begin.m_month = 7;
                begin.m_day = 11;
                end.m_month = 8;
                end.m_day = 10;
                break;
            case cMidAutumn:
            case cMidFall:
                begin.m_month = 10;
                begin.m_day = 11;
                end.m_month = 11;
                end.m_day = 10;
                break;
            case cMidWinter:
                begin.m_month = 1;
                begin.m_day = 11;
                end.m_month = 2;
                end.m_day = 10;
                break;
            case cLateSpring:
                begin.m_month = 5;
                begin.m_day = 11;
                end.m_month = 6;
                end.m_day = 20;
                break;
            case cLateSummer:
                begin.m_month = 8;
                begin.m_day = 11;
                end.m_month = 9;
                end.m_day = 20;
                break;
            case cLateAutumn:
            case cLateFall:
                begin.m_month = 11;
                begin.m_day = 11;
                end.m_month = 12;
                end.m_day = 20;
                break;
            case cLateWinter:
                begin.m_month = 2;
                begin.m_day = 11;
                end.m_month = 3;
                end.m_day = 19;
                break;
            case cSpring:
                begin.m_month = 3;
                begin.m_day = 20;
                end.m_month = 6;
                end.m_day = 20;
                break;
            case cSummer:
                begin.m_month = 6;
                begin.m_day = 21;
                end.m_month = 9;
                end.m_day = 22;
                break;
            case cAutumn:
            case cFall:
                begin.m_month = 9;
                begin.m_day = 23;
                end.m_month = 12;
                end.m_day = 20;
                break;
            case cWinter:
                begin.m_month = 12;
                begin.m_day = 21;
                end.m_month = 3;
                end.m_day = 19;
                break;
            case cEarly:
                if ((evt.m_plural) && ((evt.m_year % 100) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;
                    end.m_year = evt.m_year + 33;
                }
                else if ((evt.m_plural) && ((evt.m_year % 10) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;
                    end.m_year = evt.m_year + 3;
                }
                else
                {
                    begin.m_month = 1;
                    begin.m_day = 1;
                    end.m_month = 4;
                    end.m_day = 30;
                }

                break;
            case cMiddleOf:
                if ((evt.m_plural) && ((evt.m_year % 100) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;

                    begin.m_year = evt.m_year + 40;
                    end.m_year = evt.m_year + 60;
                }
                else if ((evt.m_plural) && ((evt.m_year % 10) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;

                    begin.m_year = evt.m_year + 4;
                    end.m_year = evt.m_year + 6;
                }
                else
                {
                    begin.m_month = 5;
                    begin.m_day = 1;
                    end.m_month = 8;
                    end.m_day = 31;
                }
                break;
            case cLate:
                if ((evt.m_plural) && ((evt.m_year % 100) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;

                    begin.m_year = evt.m_year + 70;
                    end.m_year = evt.m_year + 99;
                }
                else if ((evt.m_plural) && ((evt.m_year % 10) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;
                    begin.m_year = evt.m_year + 7;
                    end.m_year = evt.m_year + 9;
                }
                else
                {
                    begin.m_month = 9;
                    begin.m_day = 1;
                    end.m_month = 12;
                    end.m_day = 31;
                }
                break;
            case cEndOf:
                if ((evt.m_plural) && ((evt.m_year % 100) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;
                    begin.m_year = evt.m_year + 80;
                    end.m_year = evt.m_year + 99;
                }
                else if ((evt.m_plural) && ((evt.m_year % 10) == 0))
                {
                    begin.m_month = 1;
                    begin.m_day = 1;

                    end.m_month = 12;
                    end.m_day = 31;
                    begin.m_year = evt.m_year + 8;
                    end.m_year = evt.m_year + 9;
                }
                else
                {
                    begin.m_month = 11;
                    begin.m_day = 1;
                    end.m_month = 12;
                    end.m_day = 31;
                }
                break;
            }
        }
        else
        {
            begin.m_month = 1;
            begin.m_day = 1;

            end.m_month = 12;
            end.m_day = 31;

            if ((evt.m_plural) && ((evt.m_year % 100) == 0))
                end.m_year = evt.m_year + 99;
            else if ((evt.m_plural) && ((evt.m_year % 10) == 0))
                end.m_year = evt.m_year + 9;
        }
    }
    else if (evt.m_day == -1)
    {
        // month must be valid here
        assert(evt.m_month >= 1);

        // Month/year
        begin.m_month = evt.m_month;
        begin.m_day = 1;

        end.m_month = evt.m_month;
        end.m_day = 31; // doesn't need to be always valid, just has to always encompass the entire month

        if (has_prefix)
        {
            switch (evt.m_prefix)
            {
            case cEarly:
                begin.m_day = 1;
                end.m_day = 9;
                break;
            case cMiddleOf:
                begin.m_day = 10;
                end.m_day = 19;
                break;
            case cLate:
                begin.m_day = 20;
                end.m_day = 31;
                break;
            case cEndOf:
                begin.m_day = 25;
                end.m_day = 31;
                break;
            default:
                printf("Invalid prefix\n");
                break;
            }
        }
    }
    else
    {
        // Month/day/year
        begin.m_month = evt.m_month;
        begin.m_day = evt.m_day;

        end.m_month = evt.m_month;
        end.m_day = evt.m_day;
    }
}

static bool check_event_date_interval(const event_date& evt_begin, const event_date& evt_end)
{
    if ((evt_begin.m_year < 0) || (evt_begin.m_month <= 0) || (evt_begin.m_day <= 0))
        return false;

    if ((evt_end.m_year < 0) || (evt_end.m_month <= 0) || (evt_end.m_day <= 0))
        return false;

    if (evt_end.m_year < evt_begin.m_year)
    {
        return false;
    }
    else if (evt_end.m_year == evt_begin.m_year)
    {
        if (evt_end.m_month < evt_begin.m_month)
        {
            return false;
        }
        else if (evt_end.m_month == evt_begin.m_month)
        {
            if (evt_end.m_day < evt_begin.m_day)
            {
                return false;
            }
        }
    }
    return true;
}

static int compute_yearday(int month, int day, int year)
{
    assert((month >= 1) && (month <= 12));
    assert((day >= 1) && (day <= 31));
    assert(year >= 0);

    return (year * 12 * 32) + (month - 1) * 32 + (day - 1);
}

// false=reject event
// true=accept event
static bool date_filter(
    int start_month, int start_day, int start_year,
    const event_date& evt_begin, const event_date& evt_end,
    const event_date& orig_evt_begin, const event_date& orig_evt_end)
{
    // Ensure we've got a valid interval with a single span.
    if (!check_event_date_interval(evt_begin, evt_end))
    {
        panic("Invalid date range");
        return false;
    }

    if ((start_month >= 1) && (start_day >= 1) && (start_year >= 0))
    {
        // user has provided a valid month/day/year, and the event intervals are guaranteed to be fully valid, so compute the yeardays and compare

        const int evt_begin_yearday = compute_yearday(evt_begin.m_month, evt_begin.m_day, evt_begin.m_year);
        const int evt_end_yearday = compute_yearday(evt_end.m_month, evt_end.m_day, evt_end.m_year);
        assert(evt_begin_yearday <= evt_end_yearday);

        const int32_t yearday = compute_yearday(start_month, start_day, start_year);
        if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
            return true;

        return false;
    }

    if (start_month >= 1)
    {
        // Just a month, but they could have specified a year.
        if (start_year >= 0)
        {
            // month/year
            // user provided a valid month/year, do an interval check
            const int evt_begin_yearday = compute_yearday(evt_begin.m_month, 1, evt_begin.m_year);
            const int evt_end_yearday = compute_yearday(evt_end.m_month, 31, evt_end.m_year);
            assert(evt_begin_yearday <= evt_end_yearday);
                     
            const int32_t yearday = compute_yearday(start_month, 15, start_year);

            if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
                return true;

            return false;
        }
        
        // Rest have no years
        // 
        // Limit some types of searches to shorter events, otherwise the results will be overwhelming with too much noise.
        // Technically this means some very long events are dropped, but that's fine.
        const int MAX_EVENT_YEARDAYS = 31 * 6;
                
        if (start_day != -1)
        {
            // month, day, no year
            // user has provided only a valid month/day, no year, try an interval check

            // If the ORIGINAL event begins or ends on this month/day, take it
            if (((start_day == orig_evt_begin.m_day) && (start_month == orig_evt_begin.m_month)) ||
                ((start_day == orig_evt_end.m_day) && (start_month == orig_evt_end.m_month)))
                return true;
                        
            const int evt_begin_yearday = compute_yearday(evt_begin.m_month, evt_begin.m_day, 0);
            const int evt_end_yearday = compute_yearday(evt_end.m_month, evt_end.m_day, evt_end.m_year - evt_begin.m_year);
            assert(evt_begin_yearday <= evt_end_yearday);

            // Filter out very long events, they probably aren't relevant to this sort of search.
            if ((evt_end_yearday - evt_begin_yearday) <= MAX_EVENT_YEARDAYS)
            {
                // we have a complete month interval for the event, starting at year 0

                // first try the month in the first year
                int32_t yearday = compute_yearday(start_month, start_day, 0);
                if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
                    return true;

                // try 1 year later
                yearday = compute_yearday(start_month, start_day, 1);
                if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
                    return true;
            }
        }
        else
        {
            // month, no day, no year
            // user has provided only a valid month, no day/year, try an interval check

            // If the ORIGINAL event begins or ends on this month, take it
            if ((start_month == orig_evt_begin.m_month) || (start_month == orig_evt_end.m_month))
                return true;
                        
            const int evt_begin_yearday = compute_yearday(evt_begin.m_month, 1, 0);
            const int evt_end_yearday = compute_yearday(evt_end.m_month, 31, evt_end.m_year - evt_begin.m_year);
            assert(evt_begin_yearday <= evt_end_yearday);

            // Filter out very long events, they probably aren't relevant to this sort of search.
            if ((evt_end_yearday - evt_begin_yearday) <= MAX_EVENT_YEARDAYS)
            {
                // we have a complete month interval for the event, starting at year 0

                // first try the month in the first year
                int32_t yearday = compute_yearday(start_month, 15, 0);
                if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
                    return true;

                // try 1 year later
                yearday = compute_yearday(start_month, 15, 1);
                if ((evt_begin_yearday <= yearday) && (yearday <= evt_end_yearday))
                    return true;
            }
        }
    }

    return false;
}

static bool date_filter(
    int start_month, int start_day, int start_year,
    int end_month, int end_day, int end_year,
    const event_date& evt_begin, const event_date& evt_end)
{
    assert(start_month >= 1 && start_month <= 12);
    assert(start_day >= 1 && start_day <= 31);
    assert(start_year >= 0);
    assert(end_month >= 1 && end_month <= 12);
    assert(end_day >= 1 && end_day <= 31);
    assert(end_year >= 0);
    assert(start_year <= end_year);

    // Ensure we've got a valid interval with a single span.
    if (!check_event_date_interval(evt_begin, evt_end))
    {
        panic("Invalid date range");
        return false;
    }

    const int evt_begin_yearday = compute_yearday(evt_begin.m_month, evt_begin.m_day, evt_begin.m_year);
    const int evt_end_yearday = compute_yearday(evt_end.m_month, evt_end.m_day, evt_end.m_year);
    assert(evt_begin_yearday <= evt_end_yearday);

    const int32_t start_yearday = compute_yearday(start_month, start_day, start_year);
    const int32_t end_yearday = compute_yearday(end_month, end_day, end_year);
    assert(start_yearday <= end_yearday);

    // now see if there's any overlap at all between the 2 spans
    // separating axis tests
    if (evt_end_yearday < start_yearday)
        return false;
    if (evt_begin_yearday > end_yearday)
        return false;

    return true;
}

// start_year must be valid
// false=reject event
// true=accept event
static bool date_filter_single(
    int start_month, int start_day, int start_year,
    const event_date& evt_b, const event_date& evt_e)
{
    event_date evt_begin, evt_end;
    get_date_range(evt_b, evt_begin, evt_end);
    bool is_winter = (evt_begin.m_year == evt_end.m_year) && (evt_begin.m_month > evt_end.m_month);

    // evt_begin/evt_end both have valid day/months/years, but may be 1 or 2 spans (for winter)

    if (evt_e.is_valid())
    {
        event_date evt_begin2, evt_end2;
        get_date_range(evt_e, evt_begin2, evt_end2);

        // should be a valid date interval here with 1 span
        if (!check_event_date_interval(evt_begin, evt_end2))
        {
            printf("Invalid event range");
        }
        else
        {
            evt_end = evt_end2;
            is_winter = false;
        }
    }

    assert(evt_begin.m_year <= evt_end.m_year);

    // Filter by any user provided year
    if (start_year != -1)
    {
        if ((start_year < evt_begin.m_year) || (start_year > evt_end.m_year))
            return false;

        if ((start_month == -1) && (start_day == -1))
        {
            // User only provided a year to check, and it's in range so we're done.
            // This doesn't limit events based off their span because the # of results isn't overwhelming, but it could.
            return true;
        }
    }

    // Special case if they are looking for specific days with no month, possibly a year (this is the Dr. Johnson case - so let's not get too fancy for now).
    if ((start_month == -1) && (start_day >= 1))
    {
        // If there's a prefix, it's not a specific day so don't accept it.
        if ((evt_b.m_prefix != cNoPrefix) || (evt_e.m_prefix != cNoPrefix))
            return false;
        assert(!is_winter);

        // Only check timeline events that have full month/day/year, otherwise we'll pull in too many vague events
        if ((evt_b.m_month >= 1) && (evt_b.m_day >= 1))
        {
            // Handle trivial case.
            if (evt_b.m_day == start_day)
                return true;

            if (evt_e.is_valid() && (evt_e.m_month >= 1) && (evt_e.m_day >= 1))
            {
                // it's an event span - handle trivial cases.
                if (evt_e.m_day == start_day)
                    return true;

                const int b_yearday = compute_yearday(evt_b.m_month, evt_b.m_day, evt_b.m_year);
                const int e_yearday = compute_yearday(evt_e.m_month, evt_e.m_day, evt_e.m_year);

                // Ignore events longer than 14 days, they probably aren't of interest for this sort of search.
                const int MAX_TIMESPAN = 14;
                if ((e_yearday - b_yearday) <= MAX_TIMESPAN)
                {
                    // First see if the day makes sense, giving the original event's time span
                    const int t0 = compute_yearday(evt_b.m_month, start_day, evt_b.m_year);
                    if ((t0 >= b_yearday) && (t0 <= e_yearday))
                        return true;

                    // Try plugging this day into the next month
                    int nm = evt_b.m_month + 1, ny = evt_b.m_year;
                    if (nm > 12)
                    {
                        nm = 1;
                        ny++;
                    }

                    const int t1 = compute_yearday(nm, start_day, ny);
                    if ((t1 >= b_yearday) && (t1 <= e_yearday))
                        return true;
                }
            }
        }

        return false;
    }

    // We've already handled the year, day/year, or day cases.
    // Now must be month/day/year, month/year.

    if (is_winter)
    {
        // Handle 2 spans in one year
        assert(evt_begin.m_year == evt_end.m_year);

        event_date e1, e2;
        e1 = evt_begin;

        e2.m_year = evt_begin.m_year;
        e2.m_month = 12;
        e2.m_day = 31;

        bool f1 = date_filter(start_month, start_day, start_year, e1, e2, evt_b, evt_e);
        if (f1)
            return true;

        event_date e3, e4;
        e3.m_year = evt_end.m_year;
        e3.m_day = 1;
        e3.m_month = 1;

        e4.m_year = evt_end.m_year;
        e4.m_month = evt_end.m_month;
        e4.m_day = evt_end.m_day;
        bool f2 = date_filter(start_month, start_day, start_year, e3, e4, evt_b, evt_e);
        if (f2)
            return true;
    }
    else
    {
        // Only has a single span, may span years
        return date_filter(start_month, start_day, start_year, evt_begin, evt_end, evt_b, evt_e);
    }

    return false;
}

// start_year/end_years must be valid
static bool date_filter_range(
    int start_month, int start_day, int start_year,
    int end_month, int end_day, int end_year,
    const event_date& evt_b, const event_date& evt_e)
{
    if ((start_year < 0) || (end_year < 0) || (start_year > end_year))
        panic("Invalid year range");

    if (start_month < 1)
        start_month = 1;
    if (start_day < 1)
        start_day = 1;

    if (end_day < 1)
        end_day = 31;
    if (end_month < 1)
        end_month = 12;

    event_date evt_begin, evt_end;
    get_date_range(evt_b, evt_begin, evt_end);
    bool is_winter = (evt_begin.m_year == evt_end.m_year) && (evt_begin.m_month > evt_end.m_month);

    // evt_begin/evt_end both have valid day/months/years, but may be 1 or 2 spans (for winter)

    if (evt_e.is_valid())
    {
        event_date evt_begin2, evt_end2;
        get_date_range(evt_e, evt_begin2, evt_end2);

        // should be a valid date interval here with 1 span
        if (!check_event_date_interval(evt_begin, evt_end2))
        {
            printf("Invalid event range");
        }
        else
        {
            evt_end = evt_end2;
            is_winter = false;
        }
    }

    assert(evt_begin.m_year <= evt_end.m_year);
        
    if (is_winter)
    {
        // Handle 2 spans in one year
        assert(evt_begin.m_year == evt_end.m_year);

        event_date e1, e2;
        e1 = evt_begin;

        e2.m_year = evt_begin.m_year;
        e2.m_month = 12;
        e2.m_day = 31;

        bool f1 = date_filter(start_month, start_day, start_year, end_month, end_day, end_year, e1, e2);
        if (f1)
            return true;

        event_date e3, e4;
        e3.m_year = evt_end.m_year;
        e3.m_day = 1;
        e3.m_month = 1;

        e4.m_year = evt_end.m_year;
        e4.m_month = evt_end.m_month;
        e4.m_day = evt_end.m_day;
        bool f2 = date_filter(start_month, start_day, start_year, end_month, end_day, end_year, e3, e4);
        if (f2)
            return true;
    }
    else
    {
        // Only has a single span, may span years
        return date_filter(start_month, start_day, start_year, end_month, end_day, end_year, evt_begin, evt_end);
    }

    return false;
}
  
EMSCRIPTEN_KEEPALIVE
extern "C" const char* find(const char *pStr, int search_type,
    int start_month, int start_day, int start_year,
    int end_month, int end_day, int end_year,
    int max_results,
    bool brute_force_search,
    const char *pSource,
    bool most_recent_first)
{
    const double begin_time = emscripten_get_now();

    const bool is_precise_search = (search_type == cPreciseCaseSens) || (search_type == cPreciseCaseInsens);
    const bool has_source = pSource && (pSource[0] != '\0');

    g_num_results = 0;
    g_result_str.resize(0);

    if ((search_type < 0) || (search_type > cPreciseCaseInsens))
        search_type = cAll;

    printf("find() begin: str:\"%s\" st:%i, s:%i %i %i, e:%i %i %i, max: %i, bruteforce: %i, source: %s, most recent first: %i\n", 
        pStr, 
        search_type,
        start_month, start_day, start_year,
        end_month, end_day, end_year,
        max_results, 
        (int)brute_force_search, 
        pSource ? pSource : "", 
        most_recent_first);
        
    const auto& root_arr = g_doc[0];
    assert(root_arr.is_array());
        
    string_vec str_words;
    bool has_search_phrase = false;
    
    if (is_precise_search)
    {
        printf("Precise search\n");

        has_search_phrase = strlen(pStr) > 0;
    }
    else
    {
        printf("Normalizing words\n");

        get_string_words(pStr, str_words, nullptr, "-");
                
        string_vec new_str_words;

        for (uint32_t j = 0; j < str_words.size(); j++)
        {
            std::string tmp(ustrlwr(str_words[j]));
            if (!tmp.size() || is_stop_word(tmp))
                continue;

            std::string nrm_tmp(normalize_word(tmp));

            if (!nrm_tmp.size() || is_stop_word(nrm_tmp))
                continue;
            new_str_words.push_back(nrm_tmp);
        }

        if ((!new_str_words.size()) && (str_words.size()))
        {
            printf("Warning: all specified search words in the stop list! Perhaps try a precise search.\n");
            g_result_str = "## Found 0 result(s)\n\n";
            return g_result_str.c_str();
        }

        str_words.swap(new_str_words);

        printf("Num search words: %u\n", (uint32_t)str_words.size());
        for (uint32_t i = 0; i < str_words.size(); i++)
            printf("%u. \"%s\"\n", i, str_words[i].c_str());

        has_search_phrase = str_words.size() > 0;
    }
            
    uint32_t total_results = 0;

    const bool has_any_start = (start_year >= 0) || (start_day >= 1) || (start_month >= 1);
    const bool has_any_end = (end_year >= 0) || (end_day >= 1) || (end_month >= 1);

    bool use_single_date = false, use_range_date = false;
    if ((start_year >= 0) && (end_year >= 0))
    {
        // If no months provided, then clear the days.
        if (start_month < 1)
            start_day = -1;
        if (end_month < 1)
            end_day = -1;

        if (start_year > end_year)
        {
            printf("Swapping start/end dates\n");
            std::swap(start_year, end_year);
            std::swap(start_month, end_month);
            std::swap(start_day, end_day);
        }
        else if (start_year == end_year)
        {
            if (end_month < 1)
                end_month = 12;
            else if (start_month > end_month)
            {
                printf("Swapping start/end months\n");
                std::swap(start_month, end_month);
                std::swap(start_day, end_day);
            }
            else if (start_month == end_month)
            {
                if (end_day < 1)
                    end_day = 31;
                else if (start_day > end_day)
                {
                    printf("Swapping start/end days\n");
                    std::swap(start_day, end_day);
                }
            }
        }
                        
        use_range_date = true;
    }
    else if ((start_month >= 1) || (start_day >= 1) || (start_year >= 0))
    {
        use_single_date = true;
    }
    else if (end_year >= 0)
    {
        start_month = 1;
        start_day = 1;
        start_year = 0;
        
        use_range_date = true;
    }

    if (!use_single_date && !use_range_date)
    {
        if ((!has_search_phrase) && (!has_source))
        {
            printf("Nothing to search for\n");
            g_result_str = "## Found 0 result(s)\n\n";
            return g_result_str.c_str();
        }
    }
    else if (use_single_date)
        printf("Searching on single date\n");
    else if (use_range_date)
        printf("Searching on date range\n");

    printf("s:%i %i %i, e:%i %i %i\n", 
        start_month, start_day, start_year,
        end_month, end_day, end_year);
        
    uint32_vec records_to_check;
    if ((brute_force_search) || (!has_search_phrase) || (is_precise_search))
    {
        printf("Checking all records\n");

        records_to_check.resize(root_arr.size());
        for (uint32_t i = 0; i < root_arr.size(); i++)
            records_to_check[i] = i;
    }
    else
    {
        printf("Searching inverted index\n");

        std::unordered_map<uint32_t, uint32_t> record_count;
        record_count.reserve(2048);

        for (uint32_t i = 0; i < str_words.size(); i++)
        {
            auto find_it = g_word_index.find(str_words[i]);
            if (find_it == g_word_index.end())
            {
                printf("Couldn't find word \"%s\"\n", str_words[i].c_str());
                continue;
            }

            const uint32_vec& word_recs = find_it->second;

            printf("Found word \"%s\", record count: %zu\n", str_words[i].c_str(), word_recs.size());

            for (uint32_t j = 0; j < word_recs.size(); j++)
            {
                auto r = record_count.insert(std::make_pair(word_recs[j], 0));
                (r.first)->second = (r.first)->second + 1;
            }
        }

        printf("Total candidate records: %zu\n", record_count.size());
        records_to_check.resize(0);
        records_to_check.reserve(record_count.size());
        for (const auto& r : record_count)
        {
            uint32_t rec_index = r.first;
            uint32_t count = r.second;
            assert((count >= 1) && (count <= str_words.size()));

            if (search_type == cAny)
            {
                records_to_check.push_back(rec_index);
            }
            else
            {
                // cAll or cInOrder
                if (count == str_words.size())
                    records_to_check.push_back(rec_index);
                else
                {
                    //printf("Skip rec: %u, count %u\n", rec_index, count);
                }
            }
        }

        std::sort(records_to_check.begin(), records_to_check.end());
    }

    printf("Individually searching %zu total records\n", records_to_check.size());

    int min_year = INT_MAX, max_year = INT_MIN;

    std::unordered_map<uint32_t, uint32_t> year_hist;
    year_hist.reserve(256);

    int first_rec_index = 0, last_rec_index = records_to_check.size(), rec_check_iter = 1;

    if (most_recent_first)
    {
        first_rec_index = records_to_check.size() - 1;
        last_rec_index = -1;
        rec_check_iter = -1;
    }

    for (int records_to_check_iter = first_rec_index; records_to_check_iter != last_rec_index; records_to_check_iter += rec_check_iter)
    {
        const uint32_t json_arr_index = records_to_check[records_to_check_iter];
        const auto &obj = root_arr[json_arr_index];

        // Filter by date
        if (use_single_date)
        {
            if (!date_filter_single(
                start_month, start_day, start_year,
                g_event_dates[json_arr_index], g_event_end_dates[json_arr_index]))
            {
                continue;
            }
        }
        else if (use_range_date)
        {
            if (!date_filter_range(
                start_month, start_day, start_year,
                end_month, end_day, end_year,
                g_event_dates[json_arr_index], g_event_end_dates[json_arr_index]))
            {
                continue;
            }
        }

        // Filter by source
        if (has_source)
        {
            const char* pRecSource = obj.find_string_ptr("source");
            if ((!pRecSource) || (!pRecSource[0]))
                continue;
            if (strcmp(pSource, pRecSource) != 0)
                continue;
        }
        
        // Filter by search phrase
        const char* pDesc = obj.find_string_ptr("desc");
        if (!pDesc)
            continue;

        const char* pSearch = obj.find_string_ptr("search");
        if (!pSearch)
            continue;

        const pjson::value_variant* pRefs = obj.find_child_array("ref");

        const pjson::value_variant* pLocation_arr = obj.find_child_array("location");
        const char* pLocation_str = obj.find_string_ptr("location");

        const pjson::value_variant* pAttributes = obj.find_child_array("attributes");
        
        bool found_match = false;
        if ((search_type == cPreciseCaseSens) || (search_type == cPreciseCaseInsens))
        {
            found_match = check_for_match(pDesc, pStr, (search_t)search_type, str_words);

            if (!found_match)
            {
                const pjson::value_variant* pRefs = obj.find_child_array("ref");
                if (pRefs)
                {
                    for (uint32_t j = 0; j < pRefs->size(); j++)
                    {
                        const char* p = (*pRefs)[j].as_string_ptr();
                        if (p && p[0])
                        {
                            found_match = check_for_match(p, pStr, (search_t)search_type, str_words);
                            if (found_match)
                                break;
                        }
                    }
                }
                else
                {
                    const char* pRef = obj.find_string_ptr("ref");
                    if ((pRef) && (pRef[0]))
                    {
                        found_match = check_for_match(pRef, pStr, (search_t)search_type, str_words);
                    }
                }
            }

            if (!found_match)
            {
                if ((pLocation_str) && (pLocation_str[0]))
                {
                    found_match = check_for_match(pLocation_str, pStr, (search_t)search_type, str_words);
                }
                else if (pLocation_arr)
                {
                    bool is_first = true;
                    for (uint32_t i = 0; i < pLocation_arr->size(); i++)
                    {
                        const char* pLocation = (*pLocation_arr)[i].as_string_ptr();
                        if (pLocation && pLocation[0])
                        {
                            found_match = check_for_match(pLocation, pStr, (search_t)search_type, str_words);
                            if (found_match)
                                break;
                        }
                    }
                }
            }

            if (!found_match)
            {
                if (pAttributes && pAttributes->size())
                {
                    for (uint32_t j = 0; j < pAttributes->size(); j++)
                    {
                        const std::string& x = (*pAttributes)[j].as_string();

                        if (x.size())
                        {
                            found_match = check_for_match(x.c_str(), pStr, (search_t)search_type, str_words);
                            if (found_match)
                                break;
                        }
                    }
                }
            }
        }
        else
        {
            if (!str_words.size())
                found_match = true;
            else
            {
                if ((brute_force_search) || (search_type == cInOrder))
                    found_match = check_for_match(pSearch, pStr, (search_t)search_type, str_words);
                else
                {
                    // The inverted index did the work for us.
                    found_match = true;
                }
            }
        }

        if (!found_match)
            continue;

        // Print match
        const char *pURL = nullptr;            
        
        const pjson::value_variant *pKey_values = obj.find_child_object("key_vals");
        if (pKey_values)
        {
            pURL = pKey_values->find_string_ptr("url");
        }
                                
        const char *pDate = obj.find_string_ptr("date");
        if (!pDate)
            continue;
                                                                                                  
        g_result_str += "---\n\n";
        
        if (pURL)
            g_result_str += string_format("**%u. Date:** ", total_results + 1) + std::string(pURL) +  "  \n";
        else
            g_result_str += string_format("**%u. Date:** ", total_results + 1) + std::string(pDate) +  "  \n";

        const char* pAlt_date = obj.find_string_ptr("alt_date");
        if ((pAlt_date) && (pAlt_date[0]))
        {
            g_result_str += "**Alternate Date:** " + std::string(pAlt_date) + "  \n";
        }

        const char *pEnd_date = obj.find_string_ptr("end_date");
        if ((pEnd_date) && (pEnd_date[0]))
        {
            g_result_str += "**End Date:** " + std::string(pEnd_date) +  "  \n";
        }
        
        const char *pTime = obj.find_string_ptr("time");
        if ((pTime) && (pTime[0]))
        {   
            g_result_str += "**Time:** " + std::string(pTime) +  "  \n";
        }
                
        if ((pLocation_str) && (pLocation_str[0]))
        {
            g_result_str += "**Location:** " + std::string(pLocation_str) + "  \n";
        }
        else if (pLocation_arr)
        {
            g_result_str += "**Location:** ";

            bool is_first = true;
            for (uint32_t i = 0; i < pLocation_arr->size(); i++)
            {
                const char* pLocation = (*pLocation_arr)[i].as_string_ptr();
                if (pLocation && pLocation[0])
                {
                    if (!is_first)
                        g_result_str += "; ";

                    g_result_str += std::string(pLocation);
                    is_first = false;
                }
            }

            g_result_str += "  \n";
        }
        
        g_result_str += "**Description:** " + std::string(pDesc) + "  \n";
        
        const char *pType = obj.find_string_ptr("type");
        if ((pType) && (pType[0]))
        {
            g_result_str += "**Type:** " + std::string(pType) + "  \n";
        }
        
        if (pRefs)
        {
            for (uint32_t j = 0; j < pRefs->size(); j++)
            {
                const char *p = (*pRefs)[j].as_string_ptr();
                if (p && p[0])
                {
                    g_result_str += "**Reference:** " + std::string(p) + "  \n";
                }
            }
        }
        else
        {
            const char *pRef = obj.find_string_ptr("ref");
            if ((pRef) && (pRef[0]))
            {
                g_result_str += "**Reference:** " + std::string(pRef) + "  \n";
            }
        }
        
        const char *pSource_id = obj.find_string_ptr("source_id");
        if (pSource_id)
        {
            g_result_str += "**Source ID:** " + std::string(pSource_id) + "  \n";
        }
                
        if (pAttributes && pAttributes->size())
        {
            g_result_str += "  **Attributes:** ";

            for (uint32_t j = 0; j < pAttributes->size(); j++)
            {
                const std::string& x = (*pAttributes)[j].as_string();

                if ((x.size() >= 5) && (x[3] == ':') && (uisupper(x[0]) && uisupper(x[1]) && uisupper(x[2])))
                    g_result_str += string_format("**%s**%s", string_slice(x, 0, 4).c_str(), string_slice(x, 4).c_str());
                else
                    g_result_str += string_format("%s", x.c_str());

                if (j != (pAttributes->size() - 1))
                    g_result_str += ", ";
            }

            g_result_str += "  \n";
        }

        print_value_variant(g_result_str, obj, "see_also", "**See also:** %s   \n");
        print_value_variant(g_result_str, obj, "rocket_type", "**Rocket type:** %s   \n");
        print_value_variant(g_result_str, obj, "rocket_altitude", "**Rocket altitude:** %s   \n");
        print_value_variant(g_result_str, obj, "rocket_range", "**Rocket range:** %s   \n");
        print_value_variant(g_result_str, obj, "atomic_type", "**Atomic type:** %s   \n");
        print_value_variant(g_result_str, obj, "atomic_kt", "**Atomic KT:** %s   \n");
        print_value_variant(g_result_str, obj, "atomic_mt", "**Atomic MT:** %s   \n");

        const pjson::value_variant* pKey_vals = obj.find_child_object("key_vals");
        if ((pKey_vals) && (pKey_vals->is_object()) && (pKey_vals->size()))
        {
            uint32_t total_printed = 0;

            for (uint32_t j = 0; j < pKey_vals->size(); j++)
            {
                const char* pKey = pKey_vals->get_key_name_at_index(j);
                if (strcmp(pKey, "url") == 0)
                    continue;

                const char* pStr = (*pKey_vals)[j].as_string_ptr();
                if (pStr && pStr[0])
                {
                    if (!total_printed)
                        g_result_str += "  **Extra Data:** ";
                    else 
                        g_result_str += ", ";

                    g_result_str += string_format("**%s:** \"%s\"", pKey, pStr);
                    total_printed++;
                }
            }
            
            g_result_str += "  \n";
        }

        g_result_str += "\n";

        const uint32_t begin_year = g_event_dates[json_arr_index].m_year;
        year_hist[begin_year]++;
        
        min_year = std::min<int>(min_year, begin_year);
        max_year = std::max<int>(max_year, begin_year);

        if (g_event_end_dates[json_arr_index].is_valid())
            max_year = std::max<int>(max_year, g_event_end_dates[json_arr_index].m_year);
        
        total_results++;
        if (total_results >= max_results)
            break;
    }
    
    char buf[256];
    sprintf(buf, "## Found %u result(s)", total_results);
    
    std::string extra_info("\n\n");
    if (total_results)
        extra_info = string_format(", year range: %i-%i\n\n", min_year, max_year);

    g_result_str = std::string(buf) + extra_info + g_result_str;

    if (total_results)
    {
        g_result_str += "\n\n---\n\nYear histogram:\n\n```\n";

        uint32_t peak_count = 0;
        for (int y = min_year; y <= max_year; y++)
        {
            if (!year_hist.count(y))
                continue;
            
            peak_count = std::max(peak_count, year_hist[y]);
        }

        for (int y = min_year; y <= max_year; y++)
        {
            if (!year_hist.count(y))
                continue;
            
            int count = year_hist[y];
                        
            g_result_str += string_format("%4i. %4i ", y, count);

            if (peak_count >= 2)
            {
                float flt_bar_size = (float)count / (float)peak_count * 80.0f;

                int bar_size = (int)std::floor(flt_bar_size);
                for (int i = 0; i < bar_size; i++)
                    g_result_str += u8"█";

                float remaining = flt_bar_size - (float)bar_size;
                if (remaining >= .5f)
                    g_result_str += u8"▌";
            }

            g_result_str += "  \n";
        }

        g_result_str += "```\n";
    }

    const double end_time = emscripten_get_now();
    const double total_time = end_time - begin_time;

    g_result_str += string_format("\n---\nReport done (search itself took %3.3f secs)\n", total_time / 1000.0f);
                    
    g_num_results = total_results;
    
    printf("find() end\n");
                
    return g_result_str.c_str();
}

EMSCRIPTEN_KEEPALIVE
extern "C" int get_num_results() 
{
    return g_num_results;
}
