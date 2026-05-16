<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if (Schema::hasTable('offline_upload_policy')) {
            Schema::table('offline_upload_policy', function (Blueprint $table) {
                if (!Schema::hasColumn('offline_upload_policy', 'data')) {
                    $table->json('data')->nullable();
                }

                $columnsToDrop = [
                    'customer_name',
                    'mobile',
                    'email',
                    'reg_no',
                    'ic_name',
                    'policy_no',
                    'policy_type',
                    'created_by',
                ];

                foreach ($columnsToDrop as $column) {
                    if (Schema::hasColumn('offline_upload_policy', $column)) {
                        $table->dropColumn($column);
                    }
                }
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('offline_upload_policy');
    }
};
