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
        Schema::table('MenuMaster', function (Blueprint $table) {
            //
            $table->enum('is_child', ['Y', 'N'])->default('Y')->comment('applicable only on main master menu');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('MenuMaster', function (Blueprint $table) {
            //
            $table->dropColumn('is_child');
        });
    }
};
