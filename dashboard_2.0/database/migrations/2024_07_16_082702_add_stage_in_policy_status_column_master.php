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
        Schema::table('policystatus_column_master', function (Blueprint $table) {
            //
            if(!Schema::hasColumn('policystatus_column_master', 'stage'))
            {
                $table->string('stage')->nullable();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('policy_status_column_master', function (Blueprint $table) {
            //
        });
    }
};
