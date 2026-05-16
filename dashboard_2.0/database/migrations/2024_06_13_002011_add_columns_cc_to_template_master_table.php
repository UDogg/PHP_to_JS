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
        Schema::table('template_master', function (Blueprint $table) {
            if (!Schema::hasColumn('template_master', 'cc')) {
                $table->string('cc');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('template_master', function (Blueprint $table) {

            $table->dropColumn('cc');
        });
    }
};
