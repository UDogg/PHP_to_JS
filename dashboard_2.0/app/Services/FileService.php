<?php

namespace App\Services;

use Illuminate\Support\Facades\Storage;

class FileService
{
    protected $disk;
    protected $isS3;

    public function __construct()
    {
        // Automatically read from config
        $this->disk = Storage::disk(config('dashboard_storage_disk', 'public'));
        $this->isS3 = config('filesystems.default') === 's3';
    }

    /**
     * Get full path based on disk
     */
    private function buildPath($path)
    {
        if ($this->isS3) {
            return "1/motor/dashboard/" . ltrim($path, '/');
        }

        return $path; // local path
    }

    /**
     * Upload file to selected disk
     */
    public function upload($path, $file)
    {
        return $this->disk->put($this->buildPath($path), $file);
    }

    /**
     * Get file URL
     */
    public function url($path)
    {
        return $this->disk->url($this->buildPath($path));
    }

    /**
     * Download file
     */
    public function download($path)
    {
        return $this->disk->download($this->buildPath($path));
    }

    /**
     * Check if file exists
     */
    public function exists($path)
    {
        return $this->disk->exists($this->buildPath($path));
    }

    /**
     * Delete file
     */
    public function delete($path)
    {
        return $this->disk->delete($this->buildPath($path));
    }

    /**
     * Get raw file content
     */
    public function get($path)
    {
        return $this->disk->get($this->buildPath($path));
    }
}
