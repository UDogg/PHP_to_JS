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
        Schema::table('stage_master', function (Blueprint $table) {
            if(!Schema::hasColumn('stage_master','priority'))
            {
                $table->integer('priority')->nullable()->after('stage_name');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('stage_master', function (Blueprint $table) {
            $table->dropColumn('priority');
        });
    }
};
