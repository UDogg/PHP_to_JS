<?php

function replaceSubdomains($urls)
{
    $result = [];
    foreach ($urls as $url)
    {
        if (!$url) continue;

        $parsedUrl = parse_url($url);
        if (!isset($parsedUrl['host'])) continue;

        $host = $parsedUrl['host'];
        $domainParts = explode('.', $host);

        if (count($domainParts) > 2)
        {
            $mainDomain = '*.' . implode('.', array_slice($domainParts, -2));
        }
        else
        {
            $mainDomain = $host;
        }

        if (!in_array($mainDomain, $result))
        {
            $result[] = $mainDomain;
        }
    }
    return $result;
}

$env = env('APP_ENV', 'production');

return [
    'paths' => ['api/*', 'sanctum/csrf-cookie'],
    'allowed_methods' => ['*'],

    // Replace only in non-local environments
    'allowed_origins' => in_array($env, ['local', 'testing'])
        ? ['*']
        : replaceSubdomains([
            env('APP_URL'),
            env('APP_FRONTEND_URL')
        ]),
    
    // 'allowed_origins' =>
    //     replaceSubdomains([
    //         env('APP_URL'),
    //         env('APP_FRONTEND_URL'),
    //         'http://localhost:5174','http://localhost:5175','http://localhost:5176','http://localhost:5177'
    //     ]),

    'allowed_origins_patterns' => [],

    'allowed_headers' => ['*'],
    'exposed_headers' => [],
    'max_age' => 0,
    'supports_credentials' => false,
];
