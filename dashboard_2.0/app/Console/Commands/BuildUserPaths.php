<?php 

namespace App\Console\Commands;

use Illuminate\Console\Command;
use App\Models\User;
use Illuminate\Support\Facades\DB;

class BuildUserPaths extends Command
{
    protected $signature = 'users:build-paths';
    protected $description = 'Generate materialized paths for users (force-safe)';

    public function handle()
    {
        $this->info(' Building user paths...');

        DB::disableQueryLog();

        $users = User::select('id', 'reportingto', 'path')
            ->withTrashed()
            ->get()
            ->keyBy('id');

        $childrenMap = [];

        foreach ($users as $user) {
            $parentId = (int) $user->reportingto;
            $childrenMap[$parentId][] = $user->id;
        }

        $visited = [];
        $updated = 0;
        $skipped = 0;

        foreach ($users as $user) {
            if (
                empty($user->reportingto) ||
                $user->reportingto == 0 ||
                ! $users->has($user->reportingto)
            ) {
                $this->buildPath(
                    $user->id,
                    (string) $user->id,
                    $childrenMap,
                    $users,
                    $visited,
                    $updated,
                    $skipped
                );
            }
        }

        foreach ($users as $user) {
            if (!isset($visited[$user->id])) {
                $this->warn(" Forcing root for user {$user->id}");

                $this->buildPath(
                    $user->id,
                    (string) $user->id,
                    $childrenMap,
                    $users,
                    $visited,
                    $updated,
                    $skipped
                );
            }
        }

        $this->info(" DONE");
        $this->info(" Updated paths: {$updated}");
        $this->warn(" Cycles skipped: {$skipped}");
    }

    private function buildPath(
        int $userId,
        string $path,
        array &$childrenMap,
        $users,
        array &$visited,
        int &$updated,
        int &$skipped
    ) {
        if (isset($visited[$userId])) {
            $skipped++;
            return;
        }

        $visited[$userId] = true;

        $user = $users[$userId];

        if ($user->path !== $path) {
            User::where('id', $userId)->update(['path' => $path]);
            $updated++;
        }

        foreach ($childrenMap[$userId] ?? [] as $childId) {
            $this->buildPath(
                $childId,
                $path . '/' . $childId,
                $childrenMap,
                $users,
                $visited,
                $updated,
                $skipped
            );
        }
    }
}
