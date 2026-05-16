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
        Schema::table('tag_names', function (Blueprint $table) {
            // Drop the existing 'tag_id' column if it’s not already auto-incrementing
            $table->dropColumn('tag_id');
        });
        Schema::table('tag_names', function (Blueprint $table) {
            // Add 'tag_id' as auto-incrementing primary key
            $table->bigIncrements('tag_id')->first();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('tag_names', function (Blueprint $table) {
            // Reverse the changes if rolling back
            $table->dropColumn('tag_id');
        });
    }
};
